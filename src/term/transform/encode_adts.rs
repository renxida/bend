use hvmc::run::Lab;

use crate::term::{Book, Name, Rule, Term};

impl Book {
  pub fn generate_scott_adts(&mut self) {
    let mut defs = vec![];
    for (adt_name, adt) in &self.adts {
      for (ctr_name, args) in &adt.ctrs {
        let ctrs: Vec<_> = adt.ctrs.keys().cloned().collect();

        let lam = make_lam(self.adt_labs[adt_name], args.clone(), ctrs, ctr_name);

        let rules = vec![Rule { pats: vec![], body: lam }];
        defs.push((ctr_name.clone(), rules));
      }
    }
    for (name, rules) in defs {
      self.insert_def(name, rules);
    }
  }
}

fn make_lam(lab: Lab, ctr_args: Vec<Name>, ctrs: Vec<Name>, ctr_name: &Name) -> Term {
  let ctr = Term::Var { nam: ctr_name.clone() };

  let app = ctr_args.iter().cloned().fold(ctr, |acc, nam| Term::App {
    tag: Some(lab),
    fun: Box::new(acc),
    arg: Box::new(Term::Var { nam }),
  });

  let fold_lam = |acc, arg| Term::Lam { tag: Some(lab), nam: Some(arg), bod: Box::new(acc) };

  let lam = ctrs.into_iter().rev().fold(app, fold_lam);

  let fold_lam = |acc, arg| Term::Lam { tag: None, nam: Some(arg), bod: Box::new(acc) };

  ctr_args.into_iter().rev().fold(lam, fold_lam)
}
