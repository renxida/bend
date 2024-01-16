use std::{marker::PhantomData, ptr::NonNull, collections::HashMap};

use hvmc::{run::{Wire, Net, Port}, ast::Host};

use crate::term::{DefId, Pattern, Op};

use super::{Term, term_to_net::Labels, Name, Book};

struct BorrowedBox<'t, T> {
  /// Invariant: `inner` is mutably borrowed for `'t`, so it must not be dropped
  /// for the duration of `'t`.
  inner: NonNull<T>,
  // establish contravariance over `'t``
  __: PhantomData<fn(&'t mut ())>,
}

impl<'t, T> BorrowedBox<'t, T> {
  pub fn new(value: T) -> (&'t mut T, Self) {
    let mut inner = NonNull::from(Box::leak(Box::new(value)));
    let borrow = unsafe { &mut *inner.as_mut() };
    (borrow, BorrowedBox { inner, __: PhantomData })
  }
  pub fn place(self, into: &'t mut Box<T>) {
    unsafe {
      let into = into as *mut _;
      drop(std::ptr::read(into));
      std::ptr::write(into as *mut _, self.inner);
    };
    std::mem::forget(self);
  }
}

impl<'t, T> Drop for BorrowedBox<'t, T> {
  fn drop(&mut self) {
    if !std::thread::panicking() {
      panic!("memory leak: cannot drop BorrowedFrom")
    }
  }
}

#[test]
fn test() {
  let (r, b) = BorrowedBox::new(0);
  *r = 1;
  let mut x = Box::new(0);
  b.place(&mut x);
  *r = 2;
  assert_eq!(*x, 2);
}

enum SignedTerm<'term> {
  Pos(BorrowedBox<'term, Term>),
  Neg(&'term mut Box<Term>),
}

pub type WireUid = usize;

struct Reader<'net_ref, 'net, 'term, 'labels, 'host, 'book> {
  net: &'net_ref mut Net<'net>,
  vars: HashMap<WireUid, SignedTerm<'term>>,
  labels: &'labels Labels,
  book: &'book Book,
  // Dups float in the top level 
  dups: Vec<(Name, Name, Box<Term>)>,
  host: &'host Host,
  name_idx: u64,
}

impl<'net_ref, 'net, 'term, 'labels, 'host, 'book> Reader<'net_ref, 'net, 'term, 'labels, 'host, 'book> {
  fn generate_name(&mut self) -> Name {
    self.name_idx += 1;
    Name(format!("x{}", self.name_idx - 1))
  }
  fn get_wire_uid(&mut self, wire: Wire) -> WireUid {
    (wire.load_target().wire().as_ptr() as usize).min(wire.as_ptr() as usize)
  }
  fn read_pos(&mut self, wire: Wire, term: BorrowedBox<'term, Term>) { 
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
          self.vars.insert(id, SignedTerm::Pos(term));
        }
      },
      RtTag::Ref => {
        if port == Port::ERA {
          core::mem::forget(term)
        } else {
          todo!()
        };
      }
      RtTag::Num => {
        core::mem::forget(term)
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
            self.read_pos(port.p2, out_box);
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
                  pred_box
                );
                self.read_neg(
                  port.p1.load_target().traverse_node().p2.load_target().traverse_node().p2, 
                  nxt
                );
              },
              _ => unreachable!(),
            }
            self.read_pos(port.p2, mat_box);
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
          self.read_pos(port.p2, out_box);
        } else {
          let fst = self.generate_name();
          let fst_var = Box::new(Term::Var { nam: fst.clone() });
          let snd = self.generate_name();
          let snd_var = Term::Var { nam: snd.clone() };
          let (snd_ref, snd_box) = BorrowedBox::new(snd_var);
          let dup = Term::Dup { tag: crate::term::Tag::Static, fst: Some(fst), snd: Some(snd), val: Box::new(self.unfilled_term()), nxt: fst_var };
          let (dup_ref, dup_box) = BorrowedBox::new(dup);
          match dup_ref {
            Term::Dup { val, .. } => {
              term.place(val);
              self.read_pos(port.p1, dup_box);
              self.read_pos(port.p2, snd_box);
            }
            x => unreachable!(),
          }
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

          self.read_pos(port.p1, var_box);

          *into = Box::new(Term::Lam { tag, nam: Some(nam), bod: Box::new(self.unfilled_term()) });
          // Fill it
          match &mut **into {
            Term::Lam { ref mut bod, .. } => {
              self.read_neg(port.p2, bod);
            }
            _ => unreachable!(),
          }
        } else {
          *into = Box::new(Term::Sup { tag: crate::term::Tag::Static, fst: Box::new(self.unfilled_term()), snd: Box::new(self.unfilled_term()) });
          match &mut **into {
            Term::Sup { ref mut fst, ref mut snd, .. } => {
              self.read_neg(port.p1, fst);
              self.read_neg(port.p2, snd);
            },
            _ => unreachable!(),
        }
        }
      },
    }
  }
}


pub fn readback(net: &mut Net, labels: &Labels, host: &Host, book: &Book) -> Box<Term> {
  let mut term = Box::new(Term::Era);
  let root = net.root.clone();
  Reader { net, vars: HashMap::new(), labels, name_idx: 0, dups: vec![], host, book }.read_neg(root.unwrap(), &mut term);
  term
}