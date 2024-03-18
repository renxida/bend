use crate::diagnostics::{Diagnostics, WarningType, ERR_INDENT_SIZE};
use hvmc::{
  ast::{name_to_val, val_to_name, Book, Tree},
  run::Val,
};
use indexmap::{IndexMap, IndexSet};
use std::fmt::Debug;

type Ref = Val;
type Stack<T> = Vec<T>;
type RefSet = IndexSet<Ref>;

#[derive(Default)]
pub struct Graph(IndexMap<Ref, RefSet>);

pub fn check_cycles(book: &Book, diagnostics: &mut Diagnostics) -> Result<(), Diagnostics> {
  diagnostics.start_pass();

  let graph = Graph::from(book);
  let cycles = graph.cycles();

  if !cycles.is_empty() {
    let msg = format!(
      "{}\n{}\n{:ERR_INDENT_SIZE$}{}\n{:ERR_INDENT_SIZE$}{}",
      "Mutual recursion cycle detected in compiled functions:",
      pretty_print_cycles(&cycles),
      "",
      "This program will expand infinitely in strict evaluation mode.",
      "",
      "Read https://github.com/HigherOrderCO/hvm-lang/blob/main/docs/lazy-definitions.md for more information."
    );

    diagnostics.add_book_warning(msg.as_str(), WarningType::MutualRecursionCycle);
  }

  diagnostics.fatal(())
}

fn pretty_print_cycles(cycles: &[Vec<Ref>]) -> String {
  cycles
    .iter()
    .enumerate()
    .map(|(i, cycle)| {
      let cycle_str =
        cycle.iter().chain(cycle.first()).cloned().map(val_to_name).collect::<Vec<_>>().join(" -> ");
      format!("{:ERR_INDENT_SIZE$}Cycle {}: {}", "", 1 + i, cycle_str)
    })
    .collect::<Vec<String>>()
    .join("\n")
}

impl Graph {
  pub fn cycles(&self) -> Vec<Vec<Ref>> {
    let mut cycles = Vec::new();
    let mut stack = Stack::new();
    let mut visited = RefSet::new();

    for r#ref in self.0.keys() {
      if !visited.contains(r#ref) {
        self.find_cycles(r#ref, &mut visited, &mut stack, &mut cycles);
      }
    }

    cycles
  }

  fn find_cycles(
    &self,
    r#ref: &Ref,
    visited: &mut RefSet,
    stack: &mut Stack<Ref>,
    cycles: &mut Vec<Vec<Ref>>,
  ) {
    // Check if the current ref is already in the stack, which indicates a cycle.
    if let Some(cycle_start) = stack.iter().position(|n| n == r#ref) {
      // If found, add the cycle to the cycles vector.
      cycles.push(stack[cycle_start ..].to_vec());
      return;
    }

    // If the ref has not been visited yet, mark it as visited.
    if visited.insert(*r#ref) {
      // Add the current ref to the stack to keep track of the path.
      stack.push(*r#ref);

      // Get the dependencies of the current ref.
      if let Some(dependencies) = self.get(r#ref) {
        // Search for cycles from each dependency.
        for dep in dependencies {
          self.find_cycles(dep, visited, stack, cycles);
        }
      }

      stack.pop();
    }
  }
}

fn collect_refs(current: Ref, tree: &Tree, graph: &mut Graph) {
  match tree {
    Tree::Ref { nam } => graph.add(current, *nam),
    Tree::Tup { lft, rgt, .. }
    | Tree::Dup { lft, rgt, .. }
    | Tree::Op2 { lft, rgt, .. }
    | Tree::Mat { sel: lft, ret: rgt }
    | Tree::Con { lft, rgt, .. } => {
      collect_refs(current, lft, graph);
      collect_refs(current, rgt, graph);
    }
    Tree::Op1 { rgt, .. } => {
      collect_refs(current, rgt, graph);
    }
    Tree::Era | Tree::Num { .. } | Tree::Var { .. } => (),
  }
}

impl From<&Book> for Graph {
  fn from(book: &Book) -> Self {
    let mut graph = Self::new();

    for (r#ref, net) in book.iter() {
      // Collect active refs from root.
      collect_refs(name_to_val(r#ref), &net.root, &mut graph);
      for (left, _) in net.rdex.iter() {
        // If left is an active reference, add to the graph.
        if let Tree::Ref { nam } = left {
          graph.add(name_to_val(r#ref), *nam);
        }
      }
    }

    graph
  }
}

impl Graph {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn add(&mut self, r#ref: Ref, dependency: Ref) {
    self.0.entry(r#ref).or_default().insert(dependency);
    self.0.entry(dependency).or_default();
  }

  pub fn get(&self, r#ref: &Ref) -> Option<&RefSet> {
    self.0.get(r#ref)
  }
}

impl Debug for Graph {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "Graph{:?}", self.0)
  }
}
