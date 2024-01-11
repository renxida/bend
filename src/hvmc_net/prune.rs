use crate::term::DefNames;
use hvmc::{
  ast::{Book, Tree},
};
use std::collections::HashSet;

pub fn prune_defs(book: &mut Book) {
  println!("{:?}", "Prune defs");
  let mut used_defs = HashSet::new();
  for def in book.values() {
    used_defs_in_tree(&def.root, &mut used_defs);
    for (a, b) in &def.rdex {
      used_defs_in_tree(a, &mut used_defs);
      used_defs_in_tree(b, &mut used_defs);
    }
  }
  println!("{:?}", used_defs);
  let used_defs = used_defs.into_iter().collect::<HashSet<_>>();
  book.retain(|nam, _| used_defs.contains(nam) || nam == DefNames::ENTRY_POINT);
}

fn used_defs_in_tree(tree: &Tree, used_defs: &mut HashSet<String>) {
  match tree {
    Tree::Ref { nam } => {
      println!("{:?}", nam);
      used_defs.insert(nam.clone());
    }
    Tree::Ctr { lft, rgt, .. }
    | Tree::Op2 { lft, rgt, .. }
    | Tree::Mat { sel: lft, ret: rgt } => {
      used_defs_in_tree(lft, used_defs);
      used_defs_in_tree(rgt, used_defs);
    }
    Tree::Op1 { rgt, .. } => {
      used_defs_in_tree(rgt, used_defs);
    }
    Tree::Var { .. } | Tree::Num { .. } | Tree::Era => (),
  }
}
