use super::{term_to_net::Labels, Book, DefId, MatchNum, Name, Op, Tag, Term};
use crate::{
  net::{INet, NodeId, NodeKind::*, Port, SlotId, ROOT},
  term::Pattern,
};
use std::collections::{HashMap, HashSet};
use indexmap::IndexSet;


// TODO: Display scopeless lambdas as such
/// Converts an Interaction-INet to a Lambda Calculus term
pub fn net_to_term(net: &INet, book: &Book, labels: &Labels, linear: bool) -> (Term, Vec<ReadbackError>) {
  let mut reader = Reader {
    net,
    labels,
    book,
    dup_paths: if linear { None } else { Some(Default::default()) },
    scope: Default::default(),
    namegen: Default::default(),
    seen: Default::default(),
    errors: Default::default(),
  };

  let mut term = reader.read_term(net.enter_port(ROOT));

  while let Some(node) = reader.scope.pop() {
    let val = reader.read_term(reader.net.enter_port(Port(node, 0)));
    let fst = reader.namegen.decl_name(net, Port(node, 1));
    let snd = reader.namegen.decl_name(net, Port(node, 2));

    let tag = match reader.net.node(node).kind {
      Tup => None,
      Dup { lab } => Some(reader.labels.dup.to_tag(Some(lab as u32))),
      _ => unreachable!(),
    };

    let split = &mut Split { tag, fst, snd, val };

    let uses = term.insert_split(split, usize::MAX).unwrap();
    let result = term.insert_split(split, uses);
    debug_assert_eq!(result, None);
  }

  reader.resugar_adts(&mut term);

  (term, reader.errors)
}

#[derive(Debug)]
pub enum ReadbackError {
  InvalidNumericMatch,
  ReachedRoot,
  Cyclic,
  InvalidBind,
  InvalidAdt,
  InvalidAdtMatch,
  InvalidStrTerm,
}

struct Reader<'a> {
  net: &'a INet,
  labels: &'a Labels,
  book: &'a Book,
  dup_paths: Option<HashMap<u32, Vec<SlotId>>>,
  scope: Scope,
  namegen: NameGen,
  seen: HashSet<Port>,
  errors: Vec<ReadbackError>,
}

impl<'a> Reader<'a> {
  fn read_term(&mut self, next: Port) -> Term {
    if self.dup_paths.is_none() && !self.seen.insert(next) {
      self.errors.push(ReadbackError::Cyclic);
      return Term::Var { nam: Name::new("...") };
    }

    let node = next.node();

    let term = match self.net.node(node).kind {
      Era => {
        // Only the main port actually exists in an ERA, the auxes are just an artifact of this representation.
        debug_assert!(next.slot() == 0);
        Term::Era
      }
      // If we're visiting a con node...
      Con { lab } => match next.slot() {
        // If we're visiting a port 0, then it is a lambda.
        0 => {
          let nam = self.namegen.decl_name(self.net, Port(node, 1));
          let bod = self.read_term(self.net.enter_port(Port(node, 2)));
          Term::Lam { tag: self.labels.con.to_tag(lab.map(|x| x as u32)), nam, bod: Box::new(bod) }
        }
        // If we're visiting a port 1, then it is a variable.
        1 => Term::Var { nam: self.namegen.var_name(next) },
        // If we're visiting a port 2, then it is an application.
        2 => {
          let fun = self.read_term(self.net.enter_port(Port(node, 0)));
          let arg = self.read_term(self.net.enter_port(Port(node, 1)));
          Term::App { tag: self.labels.con.to_tag(lab.map(|x| x as u32)), fun: Box::new(fun), arg: Box::new(arg) }
        }
        _ => unreachable!(),
      },
      Mat => match next.slot() {
        2 => {
          // Read the matched expression
          let scrutinee = self.read_term(self.net.enter_port(Port(node, 0)));

          // Read the pattern matching node
          let sel_node = self.net.enter_port(Port(node, 1)).node();

          // We expect the pattern matching node to be a CON
          let sel_kind = self.net.node(sel_node).kind;
          if sel_kind != (Con { lab: None }) {
            // TODO: Is there any case where we expect a different node type here on readback?
            self.errors.push(ReadbackError::InvalidNumericMatch);
            Term::new_native_match(scrutinee, Term::Era, None, Term::Era)
          } else {
            let zero_term = self.read_term(self.net.enter_port(Port(sel_node, 1)));
            let succ_term = self.read_term(self.net.enter_port(Port(sel_node, 2)));

            let Term::Lam { nam, bod, .. } = succ_term else { unreachable!() };

            Term::new_native_match(scrutinee, zero_term, nam, *bod)
          }
        }
        _ => unreachable!(),
      },
      Ref { def_id } => {
        if self.book.is_generated_def(&def_id) {
          let def = self.book.defs.get(&def_id).unwrap();
          def.assert_no_pattern_matching_rules();
          let mut term = def.rules[0].body.clone();
          term.fix_names(&mut self.namegen.id_counter, self.book);

          term
        } else {
          Term::Ref { def_id }
        }
      }
      // If we're visiting a fan node...
      Dup { lab } => match next.slot() {
        // If we're visiting a port 0, then it is a pair.
        0 => {
          if let Some(dup_paths) = &mut self.dup_paths {
            let stack = dup_paths.entry(lab as u32).or_default();
            if let Some(slot) = stack.pop() {
              // Since we had a paired Dup in the path to this Sup,
              // we "decay" the superposition according to the original direction we came from the Dup.
              let term = self.read_term(self.net.enter_port(Port(node, slot)));
              self.dup_paths.as_mut().unwrap().get_mut(&(lab as u32)).unwrap().push(slot);
              Some(term)
            } else {
              None
            }
          } else {
            None
          }
          .unwrap_or_else(|| {
            // If no Dup with same label in the path, we can't resolve the Sup, so keep it as a term.
            self.decay_or_get_ports(node).map_or_else(
              |(fst, snd)| Term::Sup {
                tag: self.labels.dup.to_tag(Some(lab.into())),
                fst: Box::new(fst),
                snd: Box::new(snd),
              },
              |term| term,
            )
          })
        }
        // If we're visiting a port 1 or 2, then it is a variable.
        // Also, that means we found a dup, so we store it to read later.
        1 | 2 => {
          if let Some(dup_paths) = &mut self.dup_paths {
            dup_paths.entry(lab as u32).or_default().push(next.slot());
            let term = self.read_term(self.net.enter_port(Port(node, 0)));
            self.dup_paths.as_mut().unwrap().entry(lab as u32).or_default().pop().unwrap();
            term
          } else {
            self.scope.insert(node);
            Term::Var { nam: self.namegen.var_name(next) }
          }
        }
        _ => unreachable!(),
      },
      Num { val } => Term::Num { val },
      Op2 { opr } => match next.slot() {
        2 => {
          let fst = self.read_term(self.net.enter_port(Port(node, 0)));
          let snd = self.read_term(self.net.enter_port(Port(node, 1)));

          Term::Opx { op: Op::from_hvmc_label(opr).unwrap(), fst: Box::new(fst), snd: Box::new(snd) }
        }
        _ => unreachable!(),
      },
      Rot => self.error(ReadbackError::ReachedRoot),
      Tup => match next.slot() {
        // If we're visiting a port 0, then it is a Tup.
        0 => self
          .decay_or_get_ports(node)
          .map_or_else(|(fst, snd)| Term::Tup { fst: Box::new(fst), snd: Box::new(snd) }, |term| term),
        // If we're visiting a port 1 or 2, then it is a variable.
        1 | 2 => {
          self.scope.insert(node);
          Term::Var { nam: self.namegen.var_name(next) }
        }
        _ => unreachable!(),
      },
    };

    term
  }

  /// Enters both ports 1 and 2 of a node,  
  /// Returning a Term if is possible to simplify the net, or the Terms on the two ports of the node.  
  /// The two possible outcomes are always equivalent.
  ///   
  /// If:  
  ///  - The node Kind is CON/TUP/DUP  
  ///  - Both ports 1 and 2 are connected to the same node on slots 1 and 2 respectively  
  ///  - That node Kind is the same as the given node Kind  
  ///
  /// Then:  
  ///   Reads the port 0 of the connected node, and returns that term.
  ///
  /// Otherwise:  
  ///   Returns the terms on ports 1 and 2 of the given node.
  ///
  /// # Example
  ///
  /// ```text
  /// // λa let (a, b) = a; (a, b)
  /// ([a b] [a b])
  ///
  /// The node `(a, b)` is just a reconstruction of the destructuring of `a`,  
  /// So we can skip both steps and just return the "value" unchanged:
  ///
  /// // λa a
  /// (a a)
  /// ```
  ///
  fn decay_or_get_ports(&mut self, node: NodeId) -> Result<Term, (Term, Term)> {
    let fst_port = self.net.enter_port(Port(node, 1));
    let snd_port = self.net.enter_port(Port(node, 2));

    let node_kind = self.net.node(node).kind;

    // This is not valid for all kinds of nodes, only CON/TUP/DUP, due to their interaction rules.
    if matches!(node_kind, Con { .. } | Tup | Dup { .. }) {
      match (fst_port, snd_port) {
        (Port(fst_node, 1), Port(snd_node, 2)) if fst_node == snd_node => {
          if self.net.node(fst_node).kind == node_kind {
            self.scope.remove(&fst_node);

            let port_zero = self.net.enter_port(Port(fst_node, 0));
            let term = self.read_term(port_zero);
            return Ok(term);
          }
        }
        _ => {}
      }
    }

    let fst = self.read_term(fst_port);
    let snd = self.read_term(snd_port);
    Err((fst, snd))
  }
}

impl<'a> Reader<'a> {
  fn decode_str(&mut self, term: &mut Term) -> Term {
    let mut s = String::new();
    fn go(t: &mut Term, s: &mut String, rd: &mut Reader<'_>) {
      match t {
        Term::Num { val } => s.push(unsafe { char::from_u32_unchecked(*val as u32) }),
        Term::Lam { bod, .. } => go(bod, s, rd),
        Term::App { tag, arg, .. } if *tag == Tag::string_scons_head() => go(arg, s, rd),
        Term::App { fun, arg, .. } => {
          go(fun, s, rd);
          go(arg, s, rd);
        }
        Term::Var { .. } => {}
        Term::Chn { .. }
        | Term::Lnk { .. }
        | Term::Let { .. }
        | Term::Tup { .. }
        | Term::Dup { .. }
        | Term::Sup { .. }
        | Term::Str { .. }
        | Term::Opx { .. }
        | Term::Match { .. }
        | Term::Ref { .. }
        | Term::Era => rd.error(ReadbackError::InvalidStrTerm),
      }
    }
    go(term, &mut s, self);
    Term::Str { val: s }
  }
}

/// Represents `let (fst, snd) = val` if `tag` is `None`, and `dup#tag fst snd = val` otherwise.
#[derive(Default)]
struct Split {
  tag: Option<Tag>,
  fst: Option<Name>,
  snd: Option<Name>,
  val: Term,
}

impl Term {
  /// Calculates the number of times `fst` and `snd` appear in this term. If
  /// that is `>= threshold`, it inserts the split at this term, and returns
  /// `None`. Otherwise, returns `Some(uses)`.
  ///
  /// This is only really useful when called in two passes – first, with
  /// `threshold = usize::MAX`, to count the number of uses, and then with
  /// `threshold = uses`.
  ///
  /// This has the effect of inserting the split at the lowest common ancestor
  /// of all of the uses of `fst` and `snd`.
  fn insert_split(&mut self, split: &mut Split, threshold: usize) -> Option<usize> {
    let n = match self {
      Term::Var { nam } => (split.fst.as_ref() == Some(nam) || split.snd.as_ref() == Some(nam)) as usize,
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => bod.insert_split(split, threshold)?,
      Term::Let { val: fst, nxt: snd, .. }
      | Term::App { fun: fst, arg: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.insert_split(split, threshold)? + snd.insert_split(split, threshold)?
      }
      Term::Match { scrutinee, arms } => {
        let mut n = scrutinee.insert_split(split, threshold)?;
        for arm in arms {
          n += arm.1.insert_split(split, threshold)?;
        }
        n
      }
      Term::Lnk { .. } | Term::Num { .. } | Term::Str { .. } | Term::Ref { .. } | Term::Era => 0,
    };
    if n >= threshold {
      let Split { tag, fst, snd, val } = std::mem::take(split);
      let nxt = Box::new(std::mem::take(self));
      *self = match tag {
        None => Term::Let {
          pat: Pattern::Tup(Box::new(Pattern::Var(fst)), Box::new(Pattern::Var(snd))),
          val: Box::new(val),
          nxt,
        },
        Some(tag) => Term::Dup { tag, fst, snd, val: Box::new(val), nxt },
      };
      None
    } else {
      Some(n)
    }
  }
}

type Scope = IndexSet<NodeId>;

#[derive(Default)]
pub struct NameGen {
  pub var_port_to_id: HashMap<Port, u64>,
  pub id_counter: u64,
}

impl NameGen {
  // Given a port, returns its name, or assigns one if it wasn't named yet.
  pub fn var_name(&mut self, var_port: Port) -> Name {
    let id = self.var_port_to_id.entry(var_port).or_insert_with(|| {
      let id = self.id_counter;
      self.id_counter += 1;
      id
    });

    Name::from_num(*id)
  }

  pub fn decl_name(&mut self, net: &INet, var_port: Port) -> Option<Name> {
    // If port is linked to an erase node, return an unused variable
    let var_use = net.enter_port(var_port);
    let var_kind = net.node(var_use.node()).kind;
    if let Era = var_kind { None } else { Some(self.var_name(var_port)) }
  }

  pub fn unique(&mut self) -> Name {
    let id = self.id_counter;
    self.id_counter += 1;
    Name::from_num(id)
  }
}

impl Op {
  pub fn from_hvmc_label(value: hvmc::ops::Op) -> Option<Op> {
    use hvmc::ops::Op as RtOp;
    match value {
      RtOp::Add => Some(Op::ADD),
      RtOp::Sub => Some(Op::SUB),
      RtOp::Mul => Some(Op::MUL),
      RtOp::Div => Some(Op::DIV),
      RtOp::Mod => Some(Op::MOD),
      RtOp::Eq  => Some(Op::EQ),
      RtOp::Ne  => Some(Op::NE),
      RtOp::Lt  => Some(Op::LT),
      RtOp::Gt  => Some(Op::GT),
      RtOp::Lte => Some(Op::LTE),
      RtOp::Gte => Some(Op::GTE),
      RtOp::And => Some(Op::AND),
      RtOp::Or  => Some(Op::OR),
      RtOp::Xor => Some(Op::XOR),
      RtOp::Lsh => Some(Op::LSH),
      RtOp::Rsh => Some(Op::RSH),
      RtOp::Not => Some(Op::NOT),
      _ => None,
    }
  }
}

impl Book {
  pub fn is_generated_def(&self, def_id: &DefId) -> bool {
    self.def_names.name(def_id).map_or(false, |Name(name)| name.contains('$'))
  }
}

impl Term {
  pub fn fix_names(&mut self, id_counter: &mut u64, book: &Book) {
    fn fix_name(nam: &mut Option<Name>, id_counter: &mut u64, bod: &mut Term) {
      if let Some(nam) = nam {
        let name = Name::from_num(*id_counter);
        *id_counter += 1;
        bod.subst(nam, &Term::Var { nam: name.clone() });
        *nam = name;
      }
    }

    match self {
      Term::Lam { nam, bod, .. } => {
        fix_name(nam, id_counter, bod);
        bod.fix_names(id_counter, book);
      }
      Term::Ref { def_id } => {
        if book.is_generated_def(def_id) {
          let def = book.defs.get(def_id).unwrap();
          def.assert_no_pattern_matching_rules();
          let mut term = def.rules[0].body.clone();
          term.fix_names(id_counter, book);
          *self = term
        }
      }
      Term::Dup { fst, snd, val, nxt, .. } => {
        val.fix_names(id_counter, book);
        fix_name(fst, id_counter, nxt);
        fix_name(snd, id_counter, nxt);
        nxt.fix_names(id_counter, book);
      }
      Term::Chn { bod, .. } => bod.fix_names(id_counter, book),
      Term::App { fun: fst, arg: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Tup { fst, snd }
      | Term::Opx { op: _, fst, snd } => {
        fst.fix_names(id_counter, book);
        snd.fix_names(id_counter, book);
      }
      Term::Match { scrutinee, arms } => {
        scrutinee.fix_names(id_counter, book);

        for (rule, term) in arms {
          if let Pattern::Num(MatchNum::Succ(Some(nam))) = rule {
            fix_name(nam, id_counter, term);
          }

          term.fix_names(id_counter, book)
        }
      }
      Term::Let { .. } => unreachable!(),
      Term::Var { .. } | Term::Lnk { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => {}
    }
  }
}

impl<'a> Reader<'a> {
  fn deref(&mut self, term: &mut Term) {
    while let Term::Ref { def_id } = term {
      let def = &self.book.defs[def_id];
      def.assert_no_pattern_matching_rules();
      *term = def.rules[0].body.clone();
      term.fix_names(&mut self.namegen.id_counter, self.book);
    }
  }
  fn resugar_adts(&mut self, term: &mut Term) {
    match term {
      Term::Lam { tag, bod, .. } if *tag == Tag::string() => *term = self.decode_str(bod),
      Term::Lam { tag: Tag::Named(adt_name), bod, .. } | Term::Chn { tag: Tag::Named(adt_name), bod, .. } => {
        let Some((adt_name, adt)) = self.book.adts.get_key_value(adt_name) else {
          return self.resugar_adts(bod);
        };
        let mut cur = &mut *term;
        let mut current_arm = None;
        for ctr in &adt.ctrs {
          self.deref(cur);
          match cur {
            Term::Lam { tag: Tag::Named(tag), nam, bod } if &*tag == adt_name => {
              if let Some(nam) = nam {
                if current_arm.is_some() {
                  return self.error(ReadbackError::InvalidAdt);
                }
                current_arm = Some((nam.clone(), ctr))
              }
              cur = bod;
            }
            _ => return self.error(ReadbackError::InvalidAdt),
          }
        }
        let Some(current_arm) = current_arm else {
          return self.error(ReadbackError::InvalidAdt);
        };
        let app = cur;
        let mut cur = &mut *app;
        for _ in current_arm.1.1 {
          self.deref(cur);
          match cur {
            Term::App { tag: Tag::Static, fun, .. } => cur = fun,
            Term::App { tag: tag @ Tag::Named(_), fun, .. } => {
              *tag = Tag::Static;
              cur = fun
            }
            _ => return self.error(ReadbackError::InvalidAdt),
          }
        }
        match cur {
          Term::Var { nam } if nam == &current_arm.0 => {}
          _ => return self.error(ReadbackError::InvalidAdt),
        }
        let def_id = self.book.def_names.def_id(current_arm.1.0).unwrap();
        *cur = Term::Ref { def_id };
        let app = std::mem::take(app);
        *term = app;
        self.resugar_adts(term);
      }
      Term::Lam { bod, .. } | Term::Chn { bod, .. } => self.resugar_adts(bod),
      Term::App { tag: Tag::Named(adt_name), fun, arg } => {
        let Some((adt_name, adt)) = self.book.adts.get_key_value(adt_name) else {
          self.resugar_adts(fun);
          self.resugar_adts(arg);
          return;
        };
        let mut cur = &mut *term;
        let mut arms = Vec::new();
        for ctr in adt.ctrs.iter().rev() {
          self.deref(cur);
          match cur {
            Term::App { tag: Tag::Named(tag), fun, arg } if &*tag == adt_name => {
              let mut args = Vec::new();
              let mut arm_term = &mut **arg;
              for _ in ctr.1 {
                self.deref(arm_term);
                if !matches!(arm_term, Term::Lam { tag: Tag::Static, .. } if &*tag == adt_name) {
                  let nam = self.namegen.unique();
                  let body = std::mem::take(arm_term);
                  *arm_term = Term::Lam {
                    tag: Tag::Static,
                    nam: Some(nam.clone()),
                    bod: Box::new(Term::App {
                      tag: Tag::Static,
                      fun: Box::new(body),
                      arg: Box::new(Term::Var { nam }),
                    }),
                  };
                }
                match arm_term {
                  Term::Lam { nam, bod, .. } => {
                    args.push(match nam {
                      Some(x) => Pattern::Var(Some(x.clone())),
                      None => Pattern::Var(None),
                    });
                    arm_term = &mut **bod;
                  }
                  _ => unreachable!(),
                }
              }
              arms.push((Pattern::Ctr(ctr.0.clone(), args), arm_term));
              cur = &mut **fun;
            }
            _ => return self.error(ReadbackError::InvalidAdtMatch),
          }
        }
        let scrutinee = std::mem::take(cur);
        let arms = arms.into_iter().rev().map(|arm| (arm.0, std::mem::take(arm.1))).collect();
        *term = Term::Match { scrutinee: Box::new(scrutinee), arms };
        self.resugar_adts(term);
      }
      Term::App { fun: fst, arg: snd, .. }
      | Term::Let { val: fst, nxt: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        self.resugar_adts(fst);
        self.resugar_adts(snd);
      }
      Term::Match { scrutinee, arms } => {
        self.resugar_adts(scrutinee);
        for arm in arms {
          self.resugar_adts(&mut arm.1);
        }
      }
      Term::Lnk { .. }
      | Term::Num { .. }
      | Term::Var { .. }
      | Term::Str { .. }
      | Term::Ref { .. }
      | Term::Era => {}
    }
  }
  fn error<T: Default>(&mut self, error: ReadbackError) -> T {
    self.errors.push(error);
    T::default()
  }
}
