use std::{marker::PhantomData, ptr::NonNull, collections::HashMap};

use hvmc::{run::{Wire, Net, Port}, ast::Host};

use crate::term::{DefId, Pattern, Op};

use super::{Term, term_to_net::Labels, Name, Book, Tag, net_to_term::ReadbackError};

use crate::borrowed_box::BorrowedBox;

pub enum SignedTerm<'term> {
  Pos(BorrowedBox<'term, Term>),
  Neg(&'term mut Box<Term>),
}

pub type WireUid = usize;

pub enum TermHole<'term> {
  Variable(BorrowedBox<'term, Term>, &'term mut Option<Name>),
  Term(BorrowedBox<'term, Term>)
}

impl<'term> TermHole<'term> {
  fn place(self, target: &'term mut Box<Term>) {
    self.term().place(target)
  }
  fn erase(self) -> bool {
    match self {
      TermHole::Variable(a, b) => {
        core::mem::forget(a);
        *b = None;
        true
      },
      TermHole::Term(a) => {
        core::mem::forget(a);
        false
      },
    }
  }
  fn term(self) -> BorrowedBox<'term, Term> {
    match self {
      TermHole::Variable(t, _) => t,
      TermHole::Term(t) => t,
    }
  }
}
impl<'term> From<BorrowedBox<'term, Term>> for TermHole<'term> {
  fn from(value: BorrowedBox<'term, Term>) -> Self {
      Self::Term(value)
  }
}
impl<'term> From<(BorrowedBox<'term, Term>, &'term mut Option<Name>)> for TermHole<'term> {
  fn from(value: (BorrowedBox<'term, Term>, &'term mut Option<Name>)) -> Self {
      Self::Variable(value.0, value.1)
  }
}

struct Reader<'book, 'area, 'term> {
  net: &'book mut Net<'area>,
  vars: HashMap<WireUid, SignedTerm<'term>>,
  labels: &'book Labels,
  book: &'book Book,
  // Dups float in the top level 
  dups: Vec<(Name, Name, Box<Term>, Tag)>,
  host: &'book Host,
  name_idx: u64,
  errors: Vec<ReadbackError>,
}

impl<'book, 'area, 'term> Reader<'book, 'area, 'term> {
  fn generate_name(&mut self) -> Name {
    self.name_idx += 1;
    Name::from_num(self.name_idx - 1)
  }
  fn get_wire_uid(&mut self, wire: Wire) -> WireUid {
    (wire.load_target().wire().as_ptr() as usize).min(wire.as_ptr() as usize)
  }
  fn read_pos(&mut self, wire: Wire, term: TermHole<'term>) { 
    use hvmc::run::Tag as RtTag;
    let port = wire.load_target();
    
    match port.tag() {
      RtTag::Red => {
        self.read_pos(port.wire(), term)
      },
      RtTag::Var => {
        let id = self.get_wire_uid(wire);
        if let Some(target) = self.vars.remove(&id) {
          match target {
            SignedTerm::Pos(_) => todo!(),
            SignedTerm::Neg(target) => {
              term.place(target)
            },
          }
        } else {
          self.vars.insert(id, SignedTerm::Pos(term.term()));
        }
      },
      RtTag::Ref => {
        if port == Port::ERA {
          term.erase();
        } else {
          todo!()
        };
      }
      RtTag::Num => {
        term.erase();
      },
      RtTag::Op2 => {
        let port = port.traverse_node();
        let fst = Box::new(self.unfilled_term());
        let snd = Box::new(self.unfilled_term());

        let out = Term::Opx { op: Op::from_hvmc_label(port.lab.try_into().unwrap()).unwrap(), fst, snd };
        let (out_ref, out_box) = BorrowedBox::new(out);
        match out_ref {
          Term::Opx { fst, snd, .. } => {
            term.place(fst);
            self.read_neg(port.p1, snd);
            self.read_pos(port.p2, out_box.into());
          }
          _ => unreachable!(),
        }
      }
      RtTag::Op1 => todo!(),
      RtTag::Mat => {
        let port = port.traverse_node();
        let zero = Box::new(self.unfilled_term());
        let succ = Box::new(self.unfilled_term());
        let scrut = Box::new(self.unfilled_term());
        let pred = self.generate_name();
        let pred_var = Term::Var { nam: pred.clone() };
        let (pred_ref, pred_box) = BorrowedBox::new(pred_var);
        /*
        let (zero_ref, zero_box) = BorrowedBox::new(zero);
        let (succ_ref, succ_box) = BorrowedBox::new(succ);
        self.read_neg(port.p1.load_target().traverse_node().p1, zero_ref);
        self.read_neg(port.p1.load_target().traverse_node().p2, succ_ref);
        */
        let mat = Term::Match { 
          scrutinee: scrut, arms: vec![
            (Pattern::Num(crate::term::MatchNum::Zero), Term::Let { pat: Pattern::Var(None), val: Box::new(Term::Era), nxt: zero }),
            (Pattern::Num(crate::term::MatchNum::Succ(Some(Some(pred)))), Term::Let { pat: Pattern::Var(None), val: Box::new(Term::Era), nxt: succ }),
          ]
        };
        let (mat_ref, mat_box) = BorrowedBox::new(mat);
        match mat_ref {
          Term::Match { scrutinee, arms } => {
            term.place(scrutinee);
            let (zero, succ) = arms.split_at_mut(1);
            match &mut zero[0].1 {
              Term::Let { nxt, .. } => {
                self.read_neg(port.p1.load_target().traverse_node().p1, nxt);
              },
              _ => unreachable!(),
            }
            match &mut succ[0].1 {
              Term::Let { nxt, .. } => {
                println!("{:?}", port.p1.load_target().traverse_node().p2.load_target().tag());
                assert!(port.p1.load_target().traverse_node().p2.load_target().tag() == RtTag::Ctr);
                self.read_pos(
                  port.p1.load_target().traverse_node().p2.load_target().traverse_node().p1,
                  pred_box.into()
                );
                self.read_neg(
                  port.p1.load_target().traverse_node().p2.load_target().traverse_node().p2, 
                  nxt
                );
              },
              _ => unreachable!(),
            }
            self.read_pos(port.p2, mat_box.into());
          }
          _ => unreachable!()
        }
      },
      RtTag::Ctr => {
        let port = port.traverse_node();
        if port.lab % 2 == 0 {
          // Even labels are CON
          let fun = Box::new(self.unfilled_term());
          let arg = Box::new(self.unfilled_term());

          let tag = self.labels.con.to_tag(if port.lab == 0 {
            None
          } else {
            Some((port.lab as u32 >> 1) - 1)
          });

          let out = Term::App { tag, fun, arg };
          let (out_ref, out_box) = BorrowedBox::new(out);
          match out_ref {
            Term::App { fun, arg, .. } => {
              term.place(fun);
              self.read_neg(port.p1, arg);
            }
            _ => unreachable!(),
          }
          self.read_pos(port.p2, out_box.into());
        } else if port.lab == 1 {
          todo!("Tup-pat")
        } else {
          let tag = self.labels.dup.to_tag(if port.lab == 1 {
            unreachable!()
          } else {
            Some((port.lab as u32 >> 1) - 1)
          });

          let fst = self.generate_name();
          let fst_var = Term::Var { nam: fst.clone() };
          let snd = self.generate_name();
          let snd_var = Term::Var { nam: snd.clone() };
          let (fst_ref, fst_box) = BorrowedBox::new(fst_var);
          let (snd_ref, snd_box) = BorrowedBox::new(snd_var);
          let fst_box: BorrowedBox<Term> = fst_box;
          //term.place(val);
          self.read_pos(port.p1, fst_box.into());
          self.read_pos(port.p2, snd_box.into());
        }
      },
    }
  }
  fn unfilled_term(&mut self) -> Term {
    Term::Var { nam: Name("sad".to_string()) }
  }
  fn read_neg(&mut self, wire: Wire, into: &'term mut Box<Term>) {
    use hvmc::run::Tag as RtTag;
    let port = wire.load_target();
    match port.tag() {
      RtTag::Red => todo!(),
      RtTag::Var => {
        let id = self.get_wire_uid(wire);
        if let Some(target) = self.vars.remove(&id) {
          match target {
            SignedTerm::Pos(target) => {
              target.place(into)
            },
            SignedTerm::Neg(_) => todo!(),
          }
        } else {
          self.vars.insert(id, SignedTerm::Neg(into));
        }
      },
      RtTag::Ref => {
        if port == Port::ERA {
          *into = Box::new(Term::Era)
        } else {
          if let Some(def_name) = self.host.back.get(&port.loc()) {
            let def_id = DefId(def_name.clone());
            if self.book.is_generated_def(&def_id) {
              let def = self.book.defs.get(&def_id).unwrap();
              def.assert_no_pattern_matching_rules();
              let mut term = def.rules[0].body.clone();
              term.fix_names(&mut self.name_idx, self.book);
              *into = Box::new(term);
            } else {
              *into = Box::new(Term::Ref { def_id })
            }
          } else {
            *into = Box::new(Term::Ref { def_id: DefId("unknown_ref".to_string()) })
          }
        }
      },
      RtTag::Num => {
        *into = Box::new(Term::Num { val: port.num() });
      },
      RtTag::Op2 => todo!(),
      RtTag::Op1 => todo!(),
      RtTag::Mat => todo!(),
      RtTag::Ctr => {
        let port = port.traverse_node();
        if port.lab % 2 == 0 {
          // Even labels are CON
          let nam = self.generate_name();
          let var = Term::Var { nam: nam.clone() };
          let (var_ref, var_box) = BorrowedBox::new(var);

          let tag = self.labels.con.to_tag(if port.lab == 0 {
            None
          } else {
            Some((port.lab as u32 >> 1) - 1)
          });


          *into = Box::new(Term::Lam { tag, nam: Some(nam), bod: Box::new(self.unfilled_term()) });
          // Fill it
          match into.as_mut() {
            Term::Lam { ref mut bod, ref mut nam, .. } => {
              self.read_pos(port.p1, (var_box, nam).into());
              self.read_neg(port.p2, bod);
            }
            _ => unreachable!(),
          }
        } else {
          if port.lab != 1 {
            let tag = (port.lab as u32 >> 1) - 1;
            let tag = self.labels.dup.to_tag(Some((port.lab as u32 >> 1) - 1));
            *into = Box::new(Term::Sup { tag, fst: Box::new(self.unfilled_term()), snd: Box::new(self.unfilled_term()) });
            match &mut **into {
              Term::Sup { ref mut fst, ref mut snd, .. } => {
                self.read_neg(port.p1, fst);
                self.read_neg(port.p2, snd);
              },
              _ => unreachable!(),
            }
          } else {
            *into = Box::new(Term::Tup { fst: Box::new(self.unfilled_term()), snd: Box::new(self.unfilled_term()) });
            match &mut **into {
              Term::Tup { ref mut fst, ref mut snd, .. } => {
                self.read_neg(port.p1, fst);
                self.read_neg(port.p2, snd);
              },
              _ => unreachable!(),
            }
          }
        }
      },
    }
  }

  fn decode_str(&mut self, term: &mut Term) -> Term {
    let mut s = String::new();
    fn go(t: &mut Term, s: &mut String, rd: &mut Reader) {
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
  
  fn deref(&mut self, term: &mut Term) {
    while let Term::Ref { def_id } = term {
      let def = &self.book.defs[def_id];
      def.assert_no_pattern_matching_rules();
      *term = def.rules[0].body.clone();
      term.fix_names(&mut self.name_idx, self.book);
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
          println!("{:?}", ctr);
          println!("{:?}", adt_name);
          match cur {
            Term::Lam { tag: Tag::Named(tag), nam, bod } if &*tag == adt_name => {
              if let Some(nam) = nam {
                if current_arm.is_some() {
                  println!("{:?}", "Two arm");
                  return self.error(ReadbackError::InvalidAdt);
                }
                current_arm = Some((nam.clone(), ctr))
              }
              cur = bod;
            }
            _ => {
                println!("{:?}", "Two aaarm");
              return self.error(ReadbackError::InvalidAdt);
            }
          }
        }
        println!("{:?}", current_arm);
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
                  let nam = self.generate_name();
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


pub fn readback(net: &mut Net, labels: &Labels, host: &Host, book: &Book) -> Box<Term> {
  let mut term = Box::new(Term::Era);
  let root = net.root.clone();
  Reader { net, vars: HashMap::new(), labels, name_idx: 0, dups: vec![], host, book, errors: vec![] }.read_neg(root.unwrap(), &mut term);
  term
}

pub fn readback_and_resugar(net: &mut Net, labels: &Labels, host: &Host, book: &Book) -> Box<Term> {
  let mut term = Box::new(Term::Era);
  let root = net.root.clone();
  let mut reader = Reader { net, vars: HashMap::new(), labels, name_idx: 0, dups: vec![], host, book, errors: vec![] };
  reader.read_neg(root.unwrap(), &mut term);
  drop(reader);
  let mut reader = Reader { net, vars: HashMap::new(), labels, name_idx: 0, dups: vec![], host, book, errors: vec![] };
  reader.resugar_adts(&mut term);
  if !reader.errors.is_empty() {
    todo!("{:?}", reader.errors);
  }
  drop(reader);
  term
}