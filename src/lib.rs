#![feature(box_patterns)]
#![feature(let_chains)]

use diagnostics::{DiagnosticOrigin, Diagnostics, DiagnosticsConfig, Severity};
use hvmc::run::Rewrites;
use hvmc_net::{pre_reduce::pre_reduce_book, prune::prune_defs};
use net::{hvmc_to_net::hvmc_to_net, net_to_hvmc::nets_to_hvmc};
use std::time::Instant;
use term::{
  book_to_nets,
  net_to_term::net_to_term,
  term_to_net::{HvmcNames, Labels},
  AdtEncoding, Book, Ctx, Term,
};

pub mod diagnostics;
pub mod hvmc_net;
pub mod net;
pub mod term;

pub use term::load_book::load_file_to_book;

pub const ENTRY_POINT: &str = "main";
pub const HVM1_ENTRY_POINT: &str = "Main";

pub fn check_book(book: &mut Book) -> Result<(), Diagnostics> {
  // TODO: Do the checks without having to do full compilation
  let res = compile_book(book, CompileOpts::light(), DiagnosticsConfig::new(Severity::Warning, false), None)?;
  print!("{}", res.diagnostics);
  Ok(())
}

pub fn compile_book(
  book: &mut Book,
  opts: CompileOpts,
  diagnostics_cfg: DiagnosticsConfig,
  args: Option<Vec<Term>>,
) -> Result<CompileResult, Diagnostics> {
  let mut diagnostics = desugar_book(book, opts, diagnostics_cfg, args)?;
  let (nets, hvmc_names, labels) = book_to_nets(book);

  let mut core_book = nets_to_hvmc(nets, &hvmc_names.hvml_to_hvmc, &mut diagnostics)?;

  if opts.pre_reduce {
    // TODO: always cross refs
    pre_reduce_book(&mut core_book, true, book.hvmc_entrypoint().to_string())?;
  }
  if opts.prune {
    prune_defs(&mut core_book, book.hvmc_entrypoint().to_string());
  }

  // TODO: Broken in this branch
  //mutual_recursion::check_cycles(&core_book, &mut diagnostics)?;

  Ok(CompileResult { core_book, labels, hvmc_names, diagnostics })
}

pub fn desugar_book(
  book: &mut Book,
  opts: CompileOpts,
  diagnostics_cfg: DiagnosticsConfig,
  args: Option<Vec<Term>>,
) -> Result<Diagnostics, Diagnostics> {
  let mut ctx = Ctx::new(book, diagnostics_cfg);

  ctx.check_shared_names();
  ctx.set_entrypoint();
  ctx.apply_args(args)?;

  ctx.book.encode_adts(opts.adt_encoding);
  ctx.book.encode_builtins();

  ctx.book.resolve_ctrs_in_pats();
  ctx.resolve_refs()?;
  ctx.check_repeated_binds();

  ctx.check_match_arity()?;
  ctx.check_unbound_pats()?;

  ctx.book.desugar_let_destructors();
  ctx.book.desugar_implicit_match_binds();

  ctx.check_ctrs_arities()?;
  // Must be between [`Book::desugar_implicit_match_binds`] and [`Ctx::linearize_matches`]
  ctx.check_unbound_vars()?;

  ctx.book.convert_match_def_to_term();

  // TODO: We give variables fresh names before the match
  // simplification to avoid `foo a a = a` binding to the wrong
  // variable (it should be the second `a`). Ideally we'd like this
  // pass to create the binds in the correct order, but to do that we
  // have to reverse the order of the created let expressions when we
  // have multiple consecutive var binds without a match in between,
  // and I couldn't think of a simple way of doing that.
  //
  // In the paper this is not a problem because all var matches are
  // pushed to the end, so it only needs to fix it in the irrefutable
  // rule case. We could maybe do the opposite and do all var matches
  // first, when it would also become easy to deal with. But this
  // would potentially generate suboptimal lambda terms, need to think
  // more about it.
  //
  // We technically still generate the let bindings in the wrong order
  // but since lets can float between the binds it uses in its body
  // and the places where its variable is used, this is not a problem.
  ctx.book.make_var_names_unique();
  ctx.simplify_matches()?;

  if opts.linearize_matches.enabled() {
    ctx.book.linearize_simple_matches(opts.linearize_matches.is_extra());
  }

  ctx.book.encode_simple_matches(opts.adt_encoding);

  // sanity check
  ctx.check_unbound_vars()?;

  ctx.book.make_var_names_unique();
  ctx.book.linearize_vars();

  // sanity check
  ctx.check_unbound_vars()?;

  // Optimizing passes
  if opts.eta {
    ctx.book.eta_reduction();
  }
  if opts.float_combinators {
    ctx.book.float_combinators();
  }
  if opts.ref_to_ref {
    ctx.simplify_ref_to_ref()?;
  }
  if opts.simplify_main {
    ctx.book.simplify_main_ref();
  }

  ctx.prune(opts.prune, opts.adt_encoding);

  if opts.inline {
    ctx.book.inline();
  }
  if opts.merge {
    ctx.book.merge_definitions();
  }

  if !ctx.info.has_errors() { Ok(ctx.info) } else { Err(ctx.info) }
}

pub fn run_book(
  mut book: Book,
  max_memory: usize,
  run_opts: RunOpts,
  compile_opts: CompileOpts,
  diagnostics_cfg: DiagnosticsConfig,
  args: Option<Vec<Term>>,
) -> Result<(Term, RunInfo), Diagnostics> {
  let CompileResult { core_book, labels, hvmc_names, diagnostics } =
    compile_book(&mut book, compile_opts, diagnostics_cfg, args)?;

  // TODO: Printing should be taken care by the cli module, but we'd
  // like to print any warnings before running so that the user can
  // cancel the run if a problem is detected.
  eprint!("{diagnostics}");

  // Run
  let debug_hook = run_opts.debug_hook(&book, &labels, &hvmc_names);

  let (res_lnet, stats) = run_compiled(&core_book, max_memory, run_opts, debug_hook, book.hvmc_entrypoint());

  let (res_term, diagnostics) =
    readback_hvmc(&res_lnet, &book, &labels, &hvmc_names, run_opts.linear, compile_opts.adt_encoding);

  let info = RunInfo { stats, diagnostics, net: res_lnet, book, labels };
  Ok((res_term, info))
}

/// Utility function to count the amount of nodes in an hvm-core AST net
pub fn count_nodes<'l>(net: &'l hvmc::ast::Net) -> usize {
  let mut visit: Vec<&'l hvmc::ast::Tree> = vec![&net.root];
  let mut count = 0usize;
  for (l, r) in &net.rdex {
    visit.push(l);
    visit.push(r);
  }
  while let Some(tree) = visit.pop() {
    match tree {
      hvmc::ast::Tree::Con { lft, rgt, .. }
      | hvmc::ast::Tree::Tup { lft, rgt, .. }
      | hvmc::ast::Tree::Op2 { lft, rgt, .. }
      | hvmc::ast::Tree::Dup { lft, rgt, .. } => {
        count += 1;
        visit.push(lft);
        visit.push(rgt);
      }
      hvmc::ast::Tree::Mat { sel, ret } => {
        count += 1;
        visit.push(sel);
        visit.push(ret);
      }
      hvmc::ast::Tree::Op1 { rgt, .. } => {
        count += 1;
        visit.push(rgt);
      }
      hvmc::ast::Tree::Var { .. } => (),
      _ => {
        count += 1;
      }
    };
  }
  count
}

pub fn run_compiled(
  book: &hvmc::ast::Book,
  mem_size: usize,
  run_opts: RunOpts,
  hook: Option<impl FnMut(&hvmc::ast::Net)>,
  entrypoint: &str,
) -> (hvmc::ast::Net, RunStats) {
  if run_opts.max_rewrites.is_some() {
    todo!("Rewrite limit not supported in this branch");
  }

  let runtime_book = hvmc::ast::book_to_runtime(book);
  let root = &mut hvmc::run::Net::init(mem_size, run_opts.lazy_mode, entrypoint);

  let start_time = Instant::now();

  if let Some(mut hook) = hook {
    expand(root, &runtime_book);
    while !rdex(root).is_empty() {
      hook(&net_from_runtime(root));
      reduce(root, &runtime_book, 1);
      expand(root, &runtime_book);
    }
  } else if run_opts.single_core {
    root.normal(&runtime_book);
  } else {
    root.parallel_normal(&runtime_book);
  }

  let elapsed = start_time.elapsed().as_secs_f64();

  let net = net_from_runtime(root);
  let stats = RunStats { rewrites: root.get_rewrites(), used: count_nodes(&net), run_time: elapsed };
  (net, stats)
}

pub fn readback_hvmc(
  net: &hvmc::ast::Net,
  book: &Book,
  labels: &Labels,
  hvmc_names: &HvmcNames,
  linear: bool,
  adt_encoding: AdtEncoding,
) -> (Term, Diagnostics) {
  let mut diags = Diagnostics::default();
  let net = hvmc_to_net(net, &hvmc_names.hvmc_to_hvml);
  let mut term = net_to_term(&net, book, labels, linear, &mut diags);

  let resugar_errs = term.resugar_adts(book, adt_encoding);
  term.resugar_builtins();

  for err in resugar_errs {
    diags.add_diagnostic(err, Severity::Warning, DiagnosticOrigin::Readback);
  }

  (term, diags)
}

trait Init {
  fn init(mem_size: usize, lazy: bool, entrypoint: &str) -> Self;
}

impl Init for hvmc::run::Net {
  // same code from Net::new but it receives the entrypoint
  fn init(size: usize, lazy: bool, entrypoint: &str) -> Self {
    if lazy {
      let mem = Box::leak(hvmc::run::Heap::<true>::init(size)) as *mut _;
      let net = hvmc::run::NetFields::<true>::new(unsafe { &*mem });
      net.boot(hvmc::ast::name_to_val(entrypoint));
      hvmc::run::Net::Lazy(hvmc::run::StaticNet { mem, net })
    } else {
      let mem = Box::leak(hvmc::run::Heap::<false>::init(size)) as *mut _;
      let net = hvmc::run::NetFields::<false>::new(unsafe { &*mem });
      net.boot(hvmc::ast::name_to_val(entrypoint));
      hvmc::run::Net::Eager(hvmc::run::StaticNet { mem, net })
    }
  }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct RunOpts {
  pub single_core: bool,
  pub debug: bool,
  pub linear: bool,
  pub lazy_mode: bool,
  pub max_memory: usize,
  pub max_rewrites: Option<usize>,
}

impl RunOpts {
  pub fn lazy() -> Self {
    Self { lazy_mode: true, single_core: true, ..Self::default() }
  }

  fn debug_hook<'a>(
    &'a self,
    book: &'a Book,
    labels: &'a Labels,
    hvmc_names: &'a HvmcNames,
  ) -> Option<impl FnMut(&hvmc::ast::Net) + 'a> {
    self.debug.then_some({
      |net: &_| {
        let net = hvmc_to_net(net, &hvmc_names.hvmc_to_hvml);
        let mut diags = Diagnostics::default();
        let res_term = net_to_term(&net, book, labels, self.linear, &mut diags);
        eprint!("{diags}");
        println!("{}\n---------------------------------------", res_term);
      }
    })
  }
}

#[derive(Clone, Copy, Debug, Default)]
pub enum OptLevel {
  #[default]
  Disabled,
  Enabled,
  Extra,
}

impl OptLevel {
  pub fn enabled(&self) -> bool {
    !matches!(self, OptLevel::Disabled)
  }

  pub fn is_extra(&self) -> bool {
    matches!(self, OptLevel::Extra)
  }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CompileOpts {
  /// Selects the encoding for the ADT syntax.
  pub adt_encoding: AdtEncoding,

  /// Enables [term::transform::eta_reduction].
  pub eta: bool,

  /// Enables [term::transform::simplify_ref_to_ref].
  pub ref_to_ref: bool,

  /// Enables [term::transform::definition_pruning] and [hvmc_net::prune].
  pub prune: bool,

  /// Enables [hvmc_net::pre_reduce].
  pub pre_reduce: bool,

  /// Enables [term::transform::linearize_matches].
  pub linearize_matches: OptLevel,

  /// Enables [term::transform::float_combinators].
  pub float_combinators: bool,

  /// Enables [term::transform::simplify_main_ref].
  pub simplify_main: bool,

  /// Enables [term::transform::definition_merge]
  pub merge: bool,

  /// Enables [term::transform::inline].
  pub inline: bool,
}

impl CompileOpts {
  /// All optimizations enabled.
  pub fn heavy() -> Self {
    Self {
      eta: true,
      ref_to_ref: true,
      prune: true,
      pre_reduce: true,
      float_combinators: true,
      simplify_main: true,
      merge: true,
      inline: true,
      adt_encoding: Default::default(),
      linearize_matches: OptLevel::Extra,
    }
  }

  /// Set all opts as true and keep the current adt encoding.
  pub fn set_all(self) -> Self {
    Self { adt_encoding: self.adt_encoding, ..Self::heavy() }
  }

  /// Set all opts as false and keep the current adt encoding.
  pub fn set_no_all(self) -> Self {
    Self { adt_encoding: self.adt_encoding, ..Self::default() }
  }

  /// All optimizations disabled, except float_combinators and linearize_matches
  pub fn light() -> Self {
    Self { float_combinators: true, linearize_matches: OptLevel::Extra, ..Self::default() }
  }

  // Disable optimizations that don't work or are unnecessary on lazy mode
  pub fn lazy_mode(&mut self) {
    self.float_combinators = false;
    if self.linearize_matches.is_extra() {
      self.linearize_matches = OptLevel::Enabled;
    }
    self.pre_reduce = false;
  }
}

impl CompileOpts {
  pub fn check(&self, lazy_mode: bool) {
    if !lazy_mode {
      if !self.float_combinators {
        println!(
          "Warning: Running in strict mode without enabling the float_combinators pass can lead to some functions expanding infinitely."
        );
      }
      if !self.linearize_matches.enabled() {
        println!(
          "Warning: Running in strict mode without enabling the linearize_matches pass can lead to some functions expanding infinitely."
        );
      }
    }
  }
}

pub struct CompileResult {
  pub diagnostics: Diagnostics,
  pub core_book: hvmc::ast::Book,
  pub labels: Labels,
  pub hvmc_names: HvmcNames,
}

pub struct RunInfo {
  pub stats: RunStats,
  pub diagnostics: Diagnostics,
  pub net: hvmc::ast::Net,
  pub book: Book,
  pub labels: Labels,
}

pub struct RunStats {
  pub rewrites: Rewrites,
  pub used: usize,
  pub run_time: f64,
}

fn expand(net: &mut hvmc::run::Net, book: &hvmc::run::Book) {
  match net {
    hvmc::run::Net::Eager(net) => net.net.expand(book),
    _ => unreachable!(),
  }
}

fn reduce(net: &mut hvmc::run::Net, book: &hvmc::run::Book, limit: usize) -> usize {
  match net {
    hvmc::run::Net::Eager(net) => net.net.reduce(book, limit),
    _ => unreachable!(),
  }
}

fn rdex(net: &mut hvmc::run::Net) -> &mut Vec<(hvmc::run::Ptr, hvmc::run::Ptr)> {
  match net {
    hvmc::run::Net::Lazy(net) => &mut net.net.rdex,
    hvmc::run::Net::Eager(net) => &mut net.net.rdex,
  }
}

fn net_from_runtime(net: &hvmc::run::Net) -> hvmc::ast::Net {
  match net {
    hvmc::run::Net::Lazy(net) => hvmc::ast::net_from_runtime(&net.net),
    hvmc::run::Net::Eager(net) => hvmc::ast::net_from_runtime(&net.net),
  }
}

fn net_to_runtime(rt_net: &mut hvmc::run::Net, net: &hvmc::ast::Net) {
  match rt_net {
    hvmc::run::Net::Lazy(rt_net) => hvmc::ast::net_to_runtime(&mut rt_net.net, net),
    hvmc::run::Net::Eager(rt_net) => hvmc::ast::net_to_runtime(&mut rt_net.net, net),
  }
}

fn runtime_net_to_runtime_def(net: &hvmc::run::Net) -> hvmc::run::Def {
  match net {
    hvmc::run::Net::Lazy(net) => hvmc::ast::runtime_net_to_runtime_def(&net.net),
    hvmc::run::Net::Eager(net) => hvmc::ast::runtime_net_to_runtime_def(&net.net),
  }
}
