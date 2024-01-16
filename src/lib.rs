#![feature(box_patterns)]
#![feature(return_position_impl_trait_in_trait)]

use hvmc::{
  ast::{show_book, Host, Net, show_net},
  run::{Area, Rewrites, Net as RtNet},
};
use hvmc_net::{pre_reduce::pre_reduce_book, prune::prune_defs};
use net::{hvmc_to_net::hvmc_to_net, net_to_hvmc::nets_to_hvmc};
use std::time::Instant;
use term::{
  book_to_nets, net_to_term,
  Book, DefId, DefNames, ReadbackError, Term,
};

pub mod hvmc_net;
pub mod net;
pub mod term;

pub use term::load_book::load_file_to_book;

use crate::term::term_to_net::Labels;

pub fn check_book(mut book: Book) -> Result<(), String> {
  // TODO: Do the checks without having to do full compilation
  compile_book(&mut book, OptimizationLevel::Light)?;
  Ok(())
}

pub fn compile_book(book: &mut Book, opt_level: OptimizationLevel) -> Result<CompileResult, String> {
  let main = desugar_book(book, opt_level)?;
  let (nets, labels) = book_to_nets(book, main);
  let mut core_book = nets_to_hvmc(nets)?;
  pre_reduce_book(&mut core_book, opt_level >= OptimizationLevel::Heavy)?;
  if opt_level >= OptimizationLevel::Heavy {
    prune_defs(&mut core_book);
  }
  Ok(CompileResult { core_book, labels, warnings: vec![] })
}

pub fn desugar_book(book: &mut Book, opt_level: OptimizationLevel) -> Result<DefId, String> {
  let main = book.check_has_main()?;
  book.check_shared_names()?;
  book.encode_strs();
  book.generate_scott_adts();
  book.resolve_refs();
  encode_pattern_matching(book)?;
  book.check_unbound_vars()?;
  book.make_var_names_unique();
  book.linearize_vars();
  if opt_level >= OptimizationLevel::Heavy {
    book.eta_reduction();
  }
  book.detach_supercombinators();
  if opt_level >= OptimizationLevel::Heavy {
    book.simplify_ref_to_ref()?;
  }
  if opt_level >= OptimizationLevel::Heavy {
    book.prune(&main);
  }
  Ok(main)
}

pub fn encode_pattern_matching(book: &mut Book) -> Result<(), String> {
  book.resolve_ctrs_in_pats();
  book.check_unbound_pats()?;
  book.desugar_let_destructors();
  book.desugar_implicit_match_binds();
  book.extract_matches()?;
  book.flatten_rules();
  let def_types = book.infer_def_types()?;
  book.check_exhaustive_patterns(&def_types)?;
  book.encode_pattern_matching_functions(&def_types);
  Ok(())
}

pub fn run_book(
  mut book: Book,
  mem_size: usize,
  parallel: bool,
  debug: bool,
  linear: bool,
  opt_level: OptimizationLevel,
) -> Result<(Term, DefNames, RunInfo), String> {
  let CompileResult { core_book, labels, warnings } = compile_book(&mut book, opt_level)?;

  if !warnings.is_empty() {
    for warn in warnings {
      eprintln!("{}", warn);
    }
    return Err("Could not run the code because of the previous warnings".into());
  }

  fn debug_hook(net: &Net, book: &Book, labels: &Labels, linear: bool) {
    let net = hvmc_to_net(net);
    let (res_term, errors) = net_to_term(&net, book, labels, linear);
    println!(
      "{}{}\n---------------------------------------",
      if errors.is_empty() { "".to_string() } else { format!("Invalid readback: {:?}\n", errors) },
      res_term.display(&book.def_names)
    );
  }
  let debug_hook =
    if debug { Some(|net: &_| debug_hook(net, &book, &labels, linear)) } else { None };

  let (res_lnet, stats) = run_compiled(&core_book, mem_size, parallel, debug_hook, &labels, &book);
  let net = hvmc_to_net(&res_lnet);
  let (res_term, readback_errors) = net_to_term(&net, &book, &labels, linear);
  let info = RunInfo { stats, readback_errors, net: res_lnet };
  Ok((res_term, book.def_names, info))
}

pub fn run_compiled(
  book: &hvmc::ast::Book,
  mem_size: usize,
  parallel: bool,
  hook: Option<impl FnMut(&Net)>,
  labels: &Labels,
  q_book: &Book
) -> (Net, RunStats) {

  let host = Host::new(book);
  let heap = RtNet::init_heap(mem_size);
  let mut root = RtNet::new(&heap);
  // Expect won't be reached because there's
  // a pass that checks this.
  root.boot(host.defs.get(DefNames::ENTRY_POINT).expect("No main function."));
  
  println!("{}",
    crate::term::readback::readback(&mut root, labels, &host, q_book)
      .display(&q_book.def_names)
  );


  let start_time = Instant::now();
  
  if let Some(mut hook) = hook {
    root.expand();
    while !root.rdex.is_empty() {
      hook(&host.readback(&root));
      root.reduce(1);
      root.expand();
    }
  } else if parallel {
    root.parallel_normal();
  } else {
    root.normal()
  }


  let elapsed = start_time.elapsed().as_secs_f64();

  let rwts = root.rwts;
  let net = host.readback(&root);
  let term = crate::term::readback::readback(&mut root, labels, &host, q_book);
  println!("{}", term.display(&q_book.def_names));

  // TODO I don't quite understand this code
  // How would it be implemented in the new version?
  // let def = runtime_net_to_runtime_def(&root);
  let stats = RunStats { rewrites: rwts, used: 0, run_time: elapsed };
  (net, stats)
}

pub fn total_rewrites(rwrts: &Rewrites) -> usize {
  rwrts.anni + rwrts.comm + rwrts.eras + rwrts.dref + rwrts.oper
}

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum OptimizationLevel {
  /// The minimum amount of transformations to produce valid hvmc outputs.
  Light,
  /// More aggressive optimizations.
  Heavy,
}

impl From<usize> for OptimizationLevel {
  fn from(value: usize) -> Self {
    if value == 0 { OptimizationLevel::Light } else { OptimizationLevel::Heavy }
  }
}

pub struct CompileResult {
  pub core_book: hvmc::ast::Book,
  pub labels: Labels,
  pub warnings: Vec<Warning>,
}

impl std::fmt::Debug for CompileResult {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for warn in &self.warnings {
      writeln!(f, "// WARNING: {}", warn)?;
    }
    write!(f, "{}", show_book(&self.core_book))
  }
}

pub enum Warning {}

impl std::fmt::Display for Warning {
  fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match *self {}
  }
}

pub struct RunInfo {
  pub stats: RunStats,
  pub readback_errors: Vec<ReadbackError>,
  pub net: Net,
}

pub struct RunStats {
  pub rewrites: Rewrites,
  pub used: usize,
  pub run_time: f64,
}
