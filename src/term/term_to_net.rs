use crate::{
  net::{
    INet,
    NodeKind::{self, *},
    Port, ROOT,
  },
  term::{num_to_name, Book, Name, NumCtr, Op, Pattern, Tag, Term},
};
use hvmc::{ast::name_to_val, run::Val};
use std::collections::{hash_map::Entry, HashMap};

#[derive(Debug, Default)]
pub struct HvmcNames {
  pub hvml_to_hvmc: HashMap<Name, Val>,
  pub hvmc_to_hvml: HashMap<Val, Name>,
}

pub fn book_to_nets(book: &Book) -> (HashMap<String, INet>, HvmcNames, Labels) {
  let mut nets = HashMap::new();
  let mut labels = Labels::default();
  let mut hvmc_names = HvmcNames::default();
  let mut generated_count = 0;

  let main = book.entrypoint.as_ref().unwrap();

  for def in book.defs.values() {
    for rule in def.rules.iter() {
      let net = term_to_compat_net(&rule.body, &mut labels);

      let name = if def.name == *main {
        book.hvmc_entrypoint().to_string()
      } else {
        def_name_to_hvmc_name(&def.name, main, &nets, &mut generated_count)
      };

      let val = name_to_val(&name);
      hvmc_names.hvml_to_hvmc.insert(def.name.clone(), val);
      hvmc_names.hvmc_to_hvml.insert(val, def.name.clone());

      nets.insert(name, net);
    }
  }

  labels.con.finish();
  labels.dup.finish();

  (nets, hvmc_names, labels)
}

/// Converts rules names to unique names compatible with hvm-core:
///   If the rule is compiler-generated: Convert the DefId value into a new name
///   If not: Truncates the rule name into 4 chars
/// Them checks if the given hashmap already contains the resulted name,
/// if it does, falls back into converting its DefId and succeeding ones until a unique name is found.
fn def_name_to_hvmc_name(
  def_name: &Name,
  entrypoint: &Name,
  nets: &HashMap<String, INet>,
  generated_count: &mut Val,
) -> String {
  fn truncate(s: &str, max_chars: usize) -> &str {
    match s.char_indices().nth(max_chars) {
      None => s,
      Some((idx, _)) => &s[.. idx],
    }
  }

  fn gen_unique_name(generated_count: &mut Val, nets: &HashMap<String, INet>) -> String {
    let mut id = *generated_count;
    *generated_count += 1;
    loop {
      let name = num_to_name(id);
      if nets.contains_key(&name) {
        id += 1;
      } else {
        return name;
      }
    }
  }

  if def_name.is_generated() {
    gen_unique_name(generated_count, nets)
  } else {
    let name = truncate(def_name, 10);
    if !(nets.contains_key(name) || entrypoint == name) {
      name.to_owned()
    } else {
      gen_unique_name(generated_count, nets)
    }
  }
}

/// Converts an IC term into an IC net.
pub fn term_to_compat_net(term: &Term, labels: &mut Labels) -> INet {
  let mut state = EncodeTermState {
    inet: Default::default(),
    scope: Default::default(),
    vars: Default::default(),
    global_vars: Default::default(),
    labels,
  };

  let main = state.encode_term(term, ROOT);

  for (decl_port, use_port) in std::mem::take(&mut state.global_vars).into_values() {
    state.inet.link(decl_port, use_port);
  }
  if Some(ROOT) != main {
    state.link_local(ROOT, main);
  }

  state.inet
}

#[derive(Debug)]
struct EncodeTermState<'a> {
  inet: INet,
  scope: HashMap<Name, Vec<usize>>,
  vars: Vec<(Port, Option<Port>)>,
  global_vars: HashMap<Name, (Port, Port)>,
  labels: &'a mut Labels,
}

impl EncodeTermState<'_> {
  /// Adds a subterm connected to `up` to the `inet`.
  /// `scope` has the current variable scope.
  /// `vars` has the information of which ports the variables are declared and used in.
  /// `global_vars` has the same information for global lambdas. Must be linked outside this function.
  /// Expects variables to be affine, refs to be stored as Refs and all names to be bound.
  fn encode_term(&mut self, term: &Term, up: Port) -> Option<Port> {
    Term::recursive_call(move || {
      match term {
        // A lambda becomes to a con node. Ports:
        // - 0: points to where the lambda occurs.
        // - 1: points to the lambda variable.
        // - 2: points to the lambda body.
        // core: (var_use bod)
        Term::Lam { tag, nam, bod } => {
          let fun = self.inet.new_node(Con { lab: self.labels.con.generate(tag) });

          self.push_scope(nam, Port(fun, 1));
          let bod = self.encode_term(bod, Port(fun, 2));
          self.pop_scope(nam, Port(fun, 1));
          self.link_local(Port(fun, 2), bod);

          Some(Port(fun, 0))
        }
        // core: (var_use bod)
        Term::Chn { tag, nam, bod } => {
          let fun = self.inet.new_node(Con { lab: self.labels.con.generate(tag) });
          if let Some(nam) = nam {
            self.global_vars.entry(nam.clone()).or_default().0 = Port(fun, 1);
          }
          let bod = self.encode_term(bod, Port(fun, 2));
          self.link_local(Port(fun, 2), bod);
          Some(Port(fun, 0))
        }
        // An application becomes to a con node too. Ports:
        // - 0: points to the function being applied.
        // - 1: points to the function's argument.
        // - 2: points to where the application occurs.
        // core: & fun ~ (arg ret) (fun not necessarily main port)
        Term::App { tag, fun, arg } => {
          let app = self.inet.new_node(Con { lab: self.labels.con.generate(tag) });

          let fun = self.encode_term(fun, Port(app, 0));
          self.link_local(Port(app, 0), fun);

          let arg = self.encode_term(arg, Port(app, 1));
          self.link_local(Port(app, 1), arg);

          Some(Port(app, 2))
        }
        // core: & cond ~  (zero succ) ret
        Term::Mat { args, rules } => {
          // At this point should be only simple num matches.
          let arg = args.iter().next().unwrap();
          debug_assert!(matches!(rules[0].pats[..], [Pattern::Num(NumCtr::Num(0))]));
          debug_assert!(matches!(rules[1].pats[..], [Pattern::Num(NumCtr::Succ(1, None))]));

          let if_ = self.inet.new_node(Mat);

          let cond = self.encode_term(arg, Port(if_, 0));
          self.link_local(Port(if_, 0), cond);

          let zero = &rules[0].body;
          let succ = &rules[1].body;

          let sel = self.inet.new_node(Con { lab: None });
          self.inet.link(Port(sel, 0), Port(if_, 1));
          let zero = self.encode_term(zero, Port(sel, 1));
          self.link_local(Port(sel, 1), zero);

          let succ = self.encode_term(succ, Port(sel, 2));
          self.link_local(Port(sel, 2), succ);

          Some(Port(if_, 2))
        }
        // A dup becomes a dup node too. Ports for dups of size 2:
        // - 0: points to the value projected.
        // - 1: points to the occurrence of the first variable.
        // - 2: points to the occurrence of the second variable.
        // core: & val ~ {lab fst snd} (val not necessarily main port)
        // Dups with more than 2 variables become a list-like node tree of n-1 nodes.
        // All the nodes of a dup tree have the same label.
        // `@x dup #i {x0 x1 x2 x3}; A` => `({i x0 {i x1 {i x2 x3}}} A)`
        Term::Dup { tag, bnd, val, nxt } => {
          let lab = self.labels.dup.generate(tag).unwrap();
          let (main, aux) = self.make_node_list(Dup { lab }, bnd.len());

          let val = self.encode_term(val, main);
          self.link_local(main, val);

          for (bnd, aux) in bnd.iter().zip(aux.iter()) {
            self.push_scope(bnd, *aux);
          }

          let nxt = self.encode_term(nxt, up);

          for (bnd, aux) in bnd.iter().rev().zip(aux.iter().rev()) {
            self.pop_scope(bnd, *aux);
          }

          nxt
        }
        Term::Var { nam } => {
          // We assume this variable to be valid, bound and correctly scoped.
          // This pass must be done before.
          debug_assert!(
            self.scope.contains_key(nam),
            "Unbound variable {nam}. Expected this check to be already done"
          );
          let var_stack = &self.scope[nam];
          let cur_var = *var_stack.last().unwrap();
          let (declare_port, use_port) = self.vars.get_mut(cur_var).unwrap();
          debug_assert!(use_port.is_none(), "Variable {nam} used more than once");
          self.inet.link(up, *declare_port);
          *use_port = Some(up);
          Some(*declare_port)
        }
        Term::Lnk { nam } => {
          self.global_vars.entry(nam.clone()).or_default().1 = up;
          None
        }
        // core: @def_id
        Term::Ref { nam: def_name } => {
          let node = self.inet.new_node(Ref { def_name: def_name.clone() });
          self.inet.link(Port(node, 1), Port(node, 2));
          self.inet.link(up, Port(node, 0));
          Some(Port(node, 0))
        }
        Term::Let { pat: Pattern::Tup(args), val, nxt } => {
          let nams = args.iter().map(|arg| if let Pattern::Var(nam) = arg { nam } else { unreachable!() });
          let (main, aux) = self.make_node_list(Tup, args.len());

          let val = self.encode_term(val, main);
          self.link_local(main, val);

          for (nam, aux) in nams.clone().zip(aux.iter()) {
            self.push_scope(nam, *aux);
          }
          let nxt = self.encode_term(nxt, up);
          for (nam, aux) in nams.rev().zip(aux.iter().rev()) {
            self.pop_scope(nam, *aux);
          }

          nxt
        }
        Term::Let { pat: Pattern::Var(None), val, nxt } => {
          let nod = self.inet.new_node(Era);
          let val = self.encode_term(val, Port(nod, 0));

          self.link_local(Port(nod, 0), val);

          self.encode_term(nxt, up)
        }
        Term::Let { .. } => unreachable!(), // Removed in earlier pass
        Term::Sup { tag, els } => {
          let lab = self.labels.dup.generate(tag).unwrap();
          let (main, aux) = self.make_node_list(Dup { lab }, els.len());

          for (el, aux) in els.iter().zip(aux) {
            let el = self.encode_term(el, aux);
            self.link_local(aux, el);
          }

          Some(main)
        }
        Term::Era => {
          let era = self.inet.new_node(Era);
          self.inet.link(Port(era, 1), Port(era, 2));
          Some(Port(era, 0))
        }
        // core: #val
        Term::Num { val } => {
          let node = self.inet.new_node(Num { val: *val });
          // This representation only has nodes of arity 2, so we connect the two aux ports that are not used.
          self.inet.link(Port(node, 1), Port(node, 2));
          Some(Port(node, 0))
        }
        Term::Str { .. } => unreachable!(), // Removed in desugar str
        Term::Lst { .. } => unreachable!(), // Removed in desugar list
        // core: & fst ~ <op snd ret>
        Term::Opx { op, fst, snd } => {
          let opx = self.inet.new_node(Op2 { opr: op.to_hvmc_label() });

          let fst_port = self.encode_term(fst, Port(opx, 0));
          self.link_local(Port(opx, 0), fst_port);

          let snd_port = self.encode_term(snd, Port(opx, 1));
          self.link_local(Port(opx, 1), snd_port);

          Some(Port(opx, 2))
        }
        Term::Tup { els } => {
          let (main, aux) = self.make_node_list(Tup, els.len());
          for (el, aux) in els.iter().zip(aux.iter()) {
            let el = self.encode_term(el, *aux);
            self.link_local(*aux, el);
          }

          Some(main)
        }
        Term::Err => unreachable!(),
      }
    })
  }

  fn push_scope(&mut self, name: &Option<Name>, decl_port: Port) {
    if let Some(name) = name {
      self.scope.entry(name.clone()).or_default().push(self.vars.len());
      self.vars.push((decl_port, None));
    }
  }

  fn pop_scope(&mut self, name: &Option<Name>, decl_port: Port) {
    if let Some(name) = name {
      self.scope.get_mut(name).unwrap().pop().unwrap();
    } else {
      let era = self.inet.new_node(Era);
      self.inet.link(decl_port, Port(era, 0));
      self.inet.link(Port(era, 1), Port(era, 2));
    }
  }

  fn link_local(&mut self, ptr_a: Port, ptr_b: Option<Port>) {
    if let Some(ptr_b) = ptr_b {
      self.inet.link(ptr_a, ptr_b);
    }
  }

  /// Adds a list-like tree of nodes of the same kind to the inet.
  /// Doesn't attach this tree to anything
  fn make_node_list(&mut self, kind: NodeKind, num_ports: usize) -> (Port, Vec<Port>) {
    debug_assert!(num_ports >= 2);
    let nodes: Vec<_> = (0 .. num_ports - 1).map(|_| self.inet.new_node(kind.clone())).collect();

    let mut up = Some(Port(nodes[0], 2));
    for &node in nodes.iter().skip(1) {
      self.link_local(Port(node, 0), up);
      up = Some(Port(node, 2));
    }

    let main_port = Port(nodes[0], 0);
    let mut aux_ports = nodes.iter().map(|n| Port(*n, 1)).collect::<Vec<_>>();
    aux_ports.push(Port(*nodes.last().unwrap(), 2));
    (main_port, aux_ports)
  }
}

impl Op {
  pub fn to_hvmc_label(self) -> hvmc::run::Lab {
    match self {
      Op::Add => hvmc::run::ADD,
      Op::Sub => hvmc::run::SUB,
      Op::Mul => hvmc::run::MUL,
      Op::Div => hvmc::run::DIV,
      Op::Mod => hvmc::run::MOD,
      Op::Eq => hvmc::run::EQ,
      Op::Ne => hvmc::run::NE,
      Op::Lt => hvmc::run::LT,
      Op::Gt => hvmc::run::GT,
      Op::Lte => hvmc::run::LTE,
      Op::Gte => hvmc::run::GTE,
      Op::And => hvmc::run::AND,
      Op::Or => hvmc::run::OR,
      Op::Xor => hvmc::run::XOR,
      Op::Shl => hvmc::run::LSH,
      Op::Shr => hvmc::run::RSH,
    }
  }
}

#[derive(Debug, Default)]
pub struct Labels {
  pub con: LabelGenerator,
  pub dup: LabelGenerator,
}

#[derive(Debug, Default)]
pub struct LabelGenerator {
  pub next: u32,
  pub name_to_label: HashMap<Name, u32>,
  pub label_to_name: HashMap<u32, Name>,
}

impl LabelGenerator {
  // If some tag and new generate a new label, otherwise return the generated label.
  // If none use the implicit label counter.
  fn generate(&mut self, tag: &Tag) -> Option<u32> {
    let mut unique = || {
      let lab = self.next;
      self.next += 1;
      lab
    };
    match tag {
      Tag::Named(name) => match self.name_to_label.entry(name.clone()) {
        Entry::Occupied(e) => Some(*e.get()),
        Entry::Vacant(e) => {
          let lab = unique();
          self.label_to_name.insert(lab, name.clone());
          Some(*e.insert(lab))
        }
      },
      Tag::Numeric(lab) => Some(*lab),
      Tag::Auto => Some(unique()),
      Tag::Static => None,
    }
  }

  pub fn to_tag(&self, label: Option<u32>) -> Tag {
    match label {
      Some(label) => match self.label_to_name.get(&label) {
        Some(name) => Tag::Named(name.clone()),
        None => Tag::Numeric(label),
      },
      None => Tag::Static,
    }
  }

  fn finish(&mut self) {
    self.next = u32::MAX;
    self.name_to_label.clear();
  }
}
