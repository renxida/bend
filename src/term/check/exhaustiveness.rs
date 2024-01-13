use itertools::Itertools;

use super::type_check::{DefinitionTypes, Type};
use crate::term::{Adt, Book, MatchNum, Name, Pattern, Rule};
use std::collections::BTreeMap;

impl Book {
  /// For each pattern-matching definition, check that any given value will match at least one of the rules.
  pub fn check_exhaustive_patterns(&self, def_types: &DefinitionTypes) -> Result<(), String> {
    for (def_id, def) in &self.defs {
      let def_name = self.def_names.name(def_id).unwrap();
      let types = &def_types[def_id];
      let rules_to_check = Vec::from_iter(0 .. def.rules.len());
      check_pattern(&mut vec![], &self.adts, &def.rules, types, rules_to_check, def_name)?;
    }
    Ok(())
  }
}

fn check_pattern(
  match_path: &mut Vec<Pattern>,
  adts: &BTreeMap<Name, Adt>,
  rules: &[Rule],
  types: &[Type],
  rules_to_check: Vec<usize>,
  def_name: &Name,
) -> Result<(), String> {
  println!("{:?}", types);
  if let Some(pat_type) = types.first() {
    match pat_type {
      // We can skip non pattern matching arguments
      Type::Any => {
        let mut match_path = match_path.clone();
        match_path.push(Pattern::Var(Some(Name::new("_"))));
        check_pattern(&mut match_path, adts, rules, &types[1 ..], rules_to_check, def_name)?
      }
      Type::Adt(adt_nam) => {
        let adt = &adts[adt_nam];
        // Find which rules match each constructor
        let mut next_rules_to_check: BTreeMap<Name, Vec<usize>> =
          BTreeMap::from_iter(adt.ctrs.keys().cloned().map(|ctr| (ctr, vec![])));
        for rule_idx in rules_to_check {
          let pat = &rules[rule_idx].pats[match_path.len()];
          match pat {
            // Rules with a var pattern are relevant to all constructors.
            Pattern::Var(_) => next_rules_to_check.values_mut().for_each(|x| x.push(rule_idx)),
            Pattern::Ctr(ctr_nam, _) => next_rules_to_check.get_mut(ctr_nam).unwrap().push(rule_idx),
            Pattern::Num(..) => todo!(),
            Pattern::Tup(..) => todo!(),
          }
        }
        // Match each constructor of the current pattern and recursively check the next pattern.
        for (ctr, rules_to_check) in next_rules_to_check {
          if rules_to_check.is_empty() {
            match_path.extend(vec![Pattern::Ctr(ctr.clone(), vec![]); types.len()]);
            let missing = match_path.iter().map(|p| p.to_string()).join(" ");
            return Err(format!(
              "Non-exhaustive pattern at definition '{}'. Hint: {} not covered.",
              def_name, missing
            ));
          } else {
            let mut match_path = match_path.clone();
            match_path.push(Pattern::Ctr(ctr, vec![]));
            check_pattern(&mut match_path, adts, rules, &types[1 ..], rules_to_check, def_name)?;
          }
        }
      }
      Type::Tup => {
        let mut match_path = match_path.clone();
        let wildcard = Some(Name::new("_"));
        match_path.push(Pattern::Tup(Pattern::Var(wildcard.clone()).into(), Pattern::Var(wildcard).into()));
        check_pattern(&mut match_path, adts, rules, &types[1 ..], rules_to_check, def_name)?
      }
      Type::Num => {
        let mut next_rules_to_check: BTreeMap<Name, Vec<usize>> =
          BTreeMap::from([(Name::new("0"), vec![]), (Name::new("+"), vec![])]);
        for rule_idx in rules_to_check {
          let pat = &rules[rule_idx].pats[match_path.len()];
          match pat {
            Pattern::Num(MatchNum::Zero) => {
              next_rules_to_check.get_mut(&Name::new("0")).unwrap().push(rule_idx);
            }
            Pattern::Num(MatchNum::Succ { .. }) => {
              next_rules_to_check.get_mut(&Name::new("+")).unwrap().push(rule_idx);
            }
            other => {
              return Err(format!("Expected a number but found '{other}' at definition '{def_name}'."));
            }
          }
        }
        for (num, rules_to_check) in next_rules_to_check {
          if rules_to_check.is_empty() {
            return Err(format!(
              "Non-exhaustive pattern at definition '{}'. Number pattern '{}' not covered at position {}.",
              def_name,
              num,
              match_path.len()
            ));
          } else {
            let mut match_path = match_path.clone();
            match_path.push(Pattern::Var(Some(num)));
            check_pattern(&mut match_path, adts, rules, &types[1 ..], rules_to_check, def_name)?;
          }
        }
      }
    }
  }
  Ok(())
}
