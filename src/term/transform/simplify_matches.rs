use crate::term::{
  check::type_check::{infer_arg_type, Type},
  Adt, Book, DefId, DefNames, Definition, Name, Rule, RulePat, Term,
};
use hvmc::run::Lab;
use indexmap::IndexSet;
use itertools::Itertools;
use std::collections::{BTreeMap, HashMap, HashSet};

impl Book {
  pub fn simplify_matches(&mut self) -> Result<(), String> {
    let mut new_rules = BTreeMap::<DefId, Definition>::new();
    for (def_id, def) in &mut self.defs {
      let def_name = self.def_names.name(def_id).unwrap().clone();
      for rule in def.rules.iter_mut() {
        rule.body.simplify_matches(
          &def_name,
          &self.adt_labs,
          &self.adts,
          &self.ctrs,
          &mut self.def_names,
          &mut new_rules,
          &mut 0,
        )?;
      }
    }
    self.defs.append(&mut new_rules);
    Ok(())
  }
}

impl Term {
  pub fn check_matches<'a>(
    pats: &[RulePat],
    adts: &'a BTreeMap<Name, Adt>,
    ctrs: &HashMap<Name, Name>,
  ) -> Result<(Name, &'a Adt), String> {
    let ty = infer_arg_type(pats.iter(), ctrs)?;

    let Type::Adt(nam) = ty else { unreachable!() };

    let Adt { ctrs } = &adts[&nam];

    let mut names = HashSet::new();
    let mut repeated = HashSet::new();
    let mut missing: HashSet<_> = ctrs.keys().collect();

    for rule in pats {
      let RulePat::Ctr(nam, _) = rule else { unreachable!() };

      if !names.insert(nam.clone()) {
        repeated.insert(nam.clone());
      }

      missing.remove(nam);
    }

    fn ctrs_plural_or_sing(n: usize) -> &'static str {
      if n > 1 { "constructors" } else { "a constructor" }
    }

    if !repeated.is_empty() {
      let constructor = ctrs_plural_or_sing(repeated.len());
      let repeated = repeated.into_iter().join(", ");
      return Err(format!("Repeated {constructor} in a match block: {repeated}"));
    }

    if !missing.is_empty() {
      let constructor = ctrs_plural_or_sing(missing.len());
      let missing = missing.into_iter().join(", ");
      return Err(format!("Missing {constructor} in a match block: {missing}"));
    }

    let adt = &adts[&nam];
    Ok((nam, adt))
  }

  pub fn simplify_matches(
    &mut self,
    def_name: &Name,
    adt_labs: &BTreeMap<Name, Lab>,
    adts: &BTreeMap<Name, Adt>,
    ctrs: &HashMap<Name, Name>,
    def_names: &mut DefNames,
    new_rules: &mut BTreeMap<DefId, Definition>,
    match_count: &mut usize,
  ) -> Result<(), String> {
    match self {
      Term::Match { arms, .. } => {
        if arms.is_empty() {
          return Err("Empty match block found".to_string());
        }

        for (_, term) in arms.iter_mut() {
          term.simplify_matches(def_name, adt_labs, adts, ctrs, def_names, new_rules, match_count)?;
        }

        let Term::Match { scrutinee, arms } = std::mem::take(self) else { unreachable!() };

        if matches!(arms[0], (RulePat::Num(_), _)) {
          *self = Term::Match {
            scrutinee,
            arms: match_native_arms(arms, def_name, def_names, new_rules, match_count),
          };
        } else {
          // the scrutinee of a match on adts should always be a var
          let Term::Var { nam } = *scrutinee else { unreachable!() };

          let rules: Vec<_> = arms
            .iter()
            .map(|(rule, _)| match rule {
              RulePat::Var(nam) => RulePat::Ctr(nam.clone(), Vec::new()),
              _ => unreachable!(),
            })
            .collect();

          let (adt_name, adt) = Term::check_matches(&rules, adts, ctrs)?;

          *match_count += 1;
          *self =
            match_adt_app(nam, adt, arms, adt_labs[&adt_name], def_name, def_names, new_rules, *match_count);
        }
      }

      Term::Lam { bod, .. } | Term::Chn { bod, .. } => {
        bod.simplify_matches(def_name, adt_labs, adts, ctrs, def_names, new_rules, match_count)?
      }

      Term::App { fun: fst, arg: snd, .. }
      | Term::Let { val: fst, nxt: snd, .. }
      | Term::Dup { val: fst, nxt: snd, .. }
      | Term::Tup { fst, snd }
      | Term::Sup { fst, snd, .. }
      | Term::Opx { fst, snd, .. } => {
        fst.simplify_matches(def_name, adt_labs, adts, ctrs, def_names, new_rules, match_count)?;
        snd.simplify_matches(def_name, adt_labs, adts, ctrs, def_names, new_rules, match_count)?;
      }

      Term::Var { .. } | Term::Lnk { .. } | Term::Num { .. } | Term::Ref { .. } | Term::Era => {}
    }

    Ok(())
  }
}

fn match_native_arms(
  arms: Vec<(RulePat, Term)>,
  def_name: &Name,
  def_names: &mut DefNames,
  new_rules: &mut BTreeMap<DefId, Definition>,
  match_count: &mut usize,
) -> Vec<(RulePat, Term)> {
  let mut new_arms = Vec::new();

  for (rule, body) in arms {
    let mut free_vars = IndexSet::new();
    body.free_vars(&mut free_vars);

    if free_vars.is_empty() {
      new_arms.push((rule, body));
      continue;
    }

    *match_count += 1;

    let body = free_vars.iter().rev().cloned().fold(body, |acc: Term, name| Term::Lam {
      tag: None,
      nam: Some(name),
      bod: Box::new(acc),
    });

    let rules = vec![Rule { pats: Vec::new(), body }];

    let name = make_def_name(def_name, &Name("pred".to_string()), *match_count);

    let def_id = def_names.insert(name.clone());
    let def = Definition { def_id, rules };
    new_rules.insert(def_id, def);

    let body = free_vars.into_iter().fold(Term::Ref { def_id }, |acc, nam| Term::App {
      tag: None,
      fun: Box::new(acc),
      arg: Box::new(Term::Var { nam }),
    });

    new_arms.push((rule, body));
  }

  new_arms
}

fn match_adt_app(
  nam: Name,
  Adt { ctrs }: &Adt,
  arms: Vec<(RulePat, Term)>,
  lab: Lab,
  def_name: &Name,
  def_names: &mut DefNames,
  new_rules: &mut BTreeMap<DefId, Definition>,
  match_count: usize,
) -> Term {
  let mut refs_to_app = Vec::new();

  let mut free_vars = IndexSet::new();
  let mut free_vars_staging = IndexSet::new();

  for (ctr_name, args) in ctrs {
    for (rule, term) in arms.iter() {
      let RulePat::Var(ctr) = rule else { unreachable!() };
      if ctr == ctr_name {
        term.free_vars(&mut free_vars_staging);
        for n in args {
          free_vars_staging.remove(&binded(&nam, n));
        }
        free_vars.extend(free_vars_staging.drain(..));
      }
    }
  }

  for (ctr_name, args) in ctrs {
    for (rule, term) in arms.iter() {
      let RulePat::Var(ctr) = rule else { unreachable!() };
      if ctr == ctr_name {
        let body = free_vars.iter().rev().cloned().fold(term.clone(), |acc: Term, name| Term::Lam {
          tag: None,
          nam: Some(name),
          bod: Box::new(acc),
        });
        let body = args.iter().rev().fold(body, |acc, n| Term::Lam {
          tag: Some(lab),
          nam: Some(binded(&nam, n)),
          bod: Box::new(acc),
        });
        let def_name = make_def_name(def_name, ctr_name, match_count);
        let rules = vec![Rule { pats: Vec::new(), body }];
        let def_id = def_names.insert(def_name.clone());
        let def = Definition { def_id, rules };
        new_rules.insert(def_id, def);
        refs_to_app.push(def_id);
      }
    }
  }

  free_vars.into_iter().fold(
    refs_to_app.into_iter().fold(Term::Var { nam }, |scrutinee, def_id| Term::App {
      tag: Some(lab),
      fun: Box::new(scrutinee),
      arg: Box::new(Term::Ref { def_id }),
    }),
    |acc, nam| Term::App { tag: None, fun: Box::new(acc), arg: Box::new(Term::Var { nam }) },
  )
}

fn binded(bind: &Name, acc: &Name) -> Name {
  Name::new(&format!("{bind}.{acc}"))
}

fn make_def_name(def_name: &Name, ctr: &Name, i: usize) -> Name {
  Name::new(&format!("{def_name}${ctr}${i}"))
}
