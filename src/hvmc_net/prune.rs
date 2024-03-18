use hvmc::ast::{val_to_name, Book, Tree};
use std::collections::HashSet;

pub fn prune_defs(book: &mut Book, entrypoint: String) {
  let mut used_defs = HashSet::new();
  // Start visiting the given entrypoint
  let mut to_visit = vec![entrypoint.clone()];

  while let Some(nam) = to_visit.pop() {
    let def = &book[&nam];
    used_defs_in_tree(&def.root, &mut used_defs, &mut to_visit);
    for (a, b) in &def.rdex {
      used_defs_in_tree(a, &mut used_defs, &mut to_visit);
      used_defs_in_tree(b, &mut used_defs, &mut to_visit);
    }
  }
  let used_defs = used_defs.into_iter().collect::<HashSet<_>>();
  book.retain(|nam, _| used_defs.contains(nam) || *nam == entrypoint);
}

fn used_defs_in_tree(tree: &Tree, used_defs: &mut HashSet<String>, to_visit: &mut Vec<String>) {
  match tree {
    Tree::Ref { nam } => {
      if used_defs.insert(val_to_name(*nam)) {
        to_visit.push(val_to_name(*nam));
      }
    }
    Tree::Con { lft, rgt }
    | Tree::Tup { lft, rgt }
    | Tree::Dup { lft, rgt, .. }
    | Tree::Op2 { lft, rgt, .. }
    | Tree::Mat { sel: lft, ret: rgt } => {
      used_defs_in_tree(lft, used_defs, to_visit);
      used_defs_in_tree(rgt, used_defs, to_visit);
    }
    Tree::Op1 { rgt, .. } => {
      used_defs_in_tree(rgt, used_defs, to_visit);
    }
    Tree::Var { .. } | Tree::Num { .. } | Tree::Era => (),
  }
}
