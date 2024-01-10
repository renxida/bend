use crate::term::{Book, MatchNum, Name, Pattern, Term};
use std::collections::HashMap;

impl Book {
  /// Checks that there are no unbound variables in all definitions.
  pub fn check_unbound_vars(&self) -> Result<(), String> {
    for def in self.defs.values() {
      // TODO: Enable when pattern matching is done
      // def.assert_no_pattern_matching_rules();
      def.rules[0].body.check_unbound_vars()?;
    }
    Ok(())
  }
}

impl Term {
  /// Checks that all variables are bound.
  /// Precondition: References have been resolved.
  pub fn check_unbound_vars(&self) -> Result<(), String> {
    let mut globals = HashMap::new();
    check_uses(self, &mut HashMap::new(), &mut globals)?;

    // Check global vars
    for (nam, (declared, used)) in globals.into_iter() {
      if used && !declared {
        return Err(format!("Unbound unscoped variable '${nam}'"));
      }
    }
    Ok(())
  }
}

/// Scope has the number of times a name was declared in the current scope
/// Globals has how many times a global var name was declared and used.
pub fn check_uses<'a>(
  term: &'a Term,
  scope: &mut HashMap<&'a Name, u64>,
  globals: &mut HashMap<&'a Name, (bool, bool)>,
) -> Result<(), String> {
  // TODO: Don't stop at the first error
  match term {
    Term::Lam { nam, bod, .. } => {
      push_scope(nam.as_ref(), scope);
      check_uses(bod, scope, globals)?;
      pop_scope(nam.as_ref(), scope);
    }
    Term::Var { nam } => {
      if !scope.contains_key(nam) {
        return Err(format!("Unbound variable '{nam}'"));
      }
    }
    Term::Chn { nam, bod, .. } => {
      globals.entry(nam).or_default().0 = true;
      check_uses(bod, scope, globals)?;
    }
    Term::Lnk { nam } => {
      globals.entry(nam).or_default().1 = true;
    }
    Term::Let { pat: Pattern::Var(nam), val, nxt } => {
      check_uses(val, scope, globals)?;
      push_scope(nam.as_ref(), scope);
      check_uses(nxt, scope, globals)?;
      pop_scope(nam.as_ref(), scope);
    }
    Term::Dup { fst, snd, val, nxt, .. }
    | Term::Let { pat: Pattern::Tup(box Pattern::Var(fst), box Pattern::Var(snd)), val, nxt } => {
      check_uses(val, scope, globals)?;
      push_scope(fst.as_ref(), scope);
      push_scope(snd.as_ref(), scope);
      check_uses(nxt, scope, globals)?;
      pop_scope(fst.as_ref(), scope);
      pop_scope(snd.as_ref(), scope);
    }
    Term::Let { .. } => unreachable!(),
    Term::App { fun, arg, .. } => {
      check_uses(fun, scope, globals)?;
      check_uses(arg, scope, globals)?;
    }
    Term::Tup { fst, snd } | Term::Sup { fst, snd, .. } | Term::Opx { fst, snd, .. } => {
      check_uses(fst, scope, globals)?;
      check_uses(snd, scope, globals)?;
    }
    Term::Match { scrutinee, arms } => {
      check_uses(scrutinee, scope, globals)?;
      for (pat, term) in arms {
        if let Pattern::Num(MatchNum::Succ(Some(nam))) = pat {
          push_scope(nam.as_ref(), scope);
        }

        check_uses(term, scope, globals)?;

        if let Pattern::Num(MatchNum::Succ(Some(nam))) = pat {
          pop_scope(nam.as_ref(), scope);
        }
      }
    }
    Term::Ref { .. } | Term::Num { .. } | Term::Str { .. } | Term::Era => (),
  }
  Ok(())
}

fn push_scope<'a>(nam: Option<&'a Name>, scope: &mut HashMap<&'a Name, u64>) {
  if let Some(nam) = nam {
    if let Some(n_declarations) = scope.get_mut(nam) {
      *n_declarations += 1;
    } else {
      scope.insert(nam, 1);
    }
  }
}

fn pop_scope(nam: Option<&Name>, scope: &mut HashMap<&Name, u64>) {
  if let Some(nam) = nam {
    let n_declarations = scope.get_mut(nam).unwrap();
    *n_declarations -= 1;
    if *n_declarations == 0 {
      scope.remove(nam);
    }
  }
}
