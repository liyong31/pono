/*********************                                                  */
/*! \file ic3car.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief CAR via Implicit Predicate Abstraction (IC3IA) implementation
**        based on
**
**        IC3 Modulo Theories via Implicit Predicate Abstraction
**            -- Alessandro Cimatti, Alberto Griggio,
**               Sergio Mover, Stefano Tonetta
**
**        and the open source implementation:
**
**        https://es-static.fbk.eu/people/griggio/ic3ia/index.html
**
**  within Pono, we are building on the bit-level IC3 instead of directly
**  on IC3Base, because a lot of the functionality is the same
**  In particular, we don't need to override either of the generalization
**  functions. Instead focusing on abstract/refine.
**
**/

#include "engines/ic3car.h"

#include <random>

#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/term_analysis.h"

using namespace smt;
using namespace std;

namespace pono {

IC3CAR::IC3CAR(const Property & p,
               const TransitionSystem & ts,
               const SmtSolver & s,
               PonoOptions opt)
    : super(p, RelationalTransitionSystem(s), s, opt),
      conc_ts_(ts, to_prover_solver_),
      ia_(conc_ts_, ts_, unroller_),
      // only mathsat interpolator supported
      interpolator_(create_interpolating_solver_for(
          SolverEnum::MSAT_INTERPOLATOR, Engine::IC3IA_CAR)),
      to_interpolator_(interpolator_),
      to_solver_(solver_),
      longest_cex_length_(0)
{
  // since we passed a fresh RelationalTransitionSystem as the main TS
  // need to point orig_ts_ to the right place
  orig_ts_ = ts;
  engine_ = Engine::IC3IA_CAR;
  approx_pregen_ = true;
}

void IC3CAR::add_important_var(Term v)
{
  if (!options_.ic3ia_track_important_vars_) {
    return;
  }

  // have to consider that original solver
  // might not be the same as the prover solver
  if (solver_ != orig_ts_.solver()) {
    v = to_prover_solver_.transfer_term(v);
  }
  logger.log(1, "Adding important variable: {}", v);
  ia_.add_important_var(v);
}

// pure virtual method implementations

IC3Formula IC3CAR::get_model_ic3formula() const
{
  TermVec conjuncts;
  conjuncts.reserve(predlbls_.size());
  Term val;
  for (const auto & p : predlbls_) {
    Term nextp = lbl2nlbl_.at(p);  // current to next
    if ((val = solver_->get_value(nextp)) == solver_true_) {
      conjuncts.push_back(nlbl2npred_.at(nextp));
      logger.log(
          3, "get_model_ic3formula model npred: {}", nlbl2npred_.at(nextp));
    } else {
      conjuncts.push_back(solver_->make_term(Not, nlbl2npred_.at(nextp)));
      logger.log(3,
                 "get_model_ic3formula model npred: {}",
                 solver_->make_term(Not, nlbl2npred_.at(nextp)));
    }
    assert(val->is_value());
  }

  return ic3formula_conjunction(conjuncts);
}

bool IC3CAR::ic3formula_check_valid(const IC3Formula & u) const
{
  // check that children are literals
  Term pred;
  Op op;
  for (const auto & c : u.children) {
    if (c->get_sort() != boolsort_) {
      logger.log(3, "ERROR IC3CAR IC3Formula contains non-boolean atom: {}", c);
      return false;
    }

    pred = c;
    op = pred->get_op();
    if (op == Not || op == BVNot) {
      pred = *(c->begin());
      assert(pred);
    }

    // expecting either a boolean variable or a predicate
    if (predset_.find(pred) == predset_.end()) {
      logger.log(3, "ERROR IC3CAR IC3Formula contains unknown atom: {}", pred);
      return false;
    }
  }

  // got through all checks without failing
  return true;
}

void IC3CAR::check_ts() const
{
  // basically a No-Op
  // no restrictions except that interpolants must be supported
  // instead of checking explicitly, just let the interpolator throw an
  // exception better than maintaining in two places
}

void IC3CAR::push_under_frame()
{
  // assert(under_frame_labels_.size() == under_frames_.size());
  // pushes an empty frame
  // under_frame_labels_.push_back(solver_->make_symbol(
      // "__under_frame_label_" + std::to_string(under_frames_.size()),
      // solver_->make_sort(BOOL)));
  under_frames_.push_back({});  // by default, the frame_ is empty
}

void IC3CAR::push_over_frontier()
{
  // next_bad_label_ =
  //    solver_->make_symbol("__next_bad_label_",
  //                          solver_->make_sort(BOOL));
  // Term next_bad =  ts_.next(bad_);
  // solver_->assert_formula(
  //       solver_->make_term(Implies, next_bad_label_, next_bad));
  // frames_.push_back({});
  // logger.log(
  //           3, "Add over frame formula {}: {}", frames_.size() - 1,
  //           solver_->make_term(Implies, next_bad_label_, next_bad));
}

void IC3CAR::initialize()
{
  if (initialized_) {
    return;
  }
  // call IC3Base::initialize()
  super::initialize();  // create boolsort and true iterm, abstract() ts
  // push_over_frontier(); // add bad
  push_under_frame();

  // add all the predicates from init and property to the abstraction
  // NOTE: abstract is called automatically in IC3Base initialize
  UnorderedTermSet preds;
  get_predicates(solver_, conc_ts_.init(), preds, false, false, true);
  size_t num_init_preds = preds.size();
  get_predicates(solver_, bad_, preds, false, false, true);
  size_t num_prop_preds = preds.size() - num_init_preds;
  for (const auto & p : preds) {
    add_predicate(p);
  }
  logger.log(1, "Number predicates found in init: {}", num_init_preds);
  logger.log(1, "Number predicates found in prop: {}", num_prop_preds);
  logger.log(1, "Total number of initial predicates: {}", preds.size());
  // more predicates will be added during refinement
  // these ones are just initial predicates

  // populate cache for existing terms in solver_
  UnorderedTermMap & cache = to_solver_.get_cache();
  Term ns;
  for (auto const & s : ts_.statevars()) {
    // common variables are next states, unless used for refinement in IC3CAR
    // then will refer to current state variables after untiming
    // need to cache both
    cache[to_interpolator_.transfer_term(s)] = s;
    ns = ts_.next(s);
    cache[to_interpolator_.transfer_term(ns)] = ns;
  }

  // need to add uninterpreted functions as well
  // first need to find them all
  // NOTE need to use get_free_symbols NOT get_free_symbolic_consts
  // because the latter ignores uninterpreted functions
  UnorderedTermSet free_symbols;
  get_free_symbols(ts_.init(), free_symbols);
  get_free_symbols(ts_.trans(), free_symbols);
  get_free_symbols(bad_, free_symbols);

  for (auto const & s : free_symbols) {
    assert(s->is_symbol());
    if (s->is_symbolic_const()) {
      // ignore constants
      continue;
    }
    cache[to_interpolator_.transfer_term(s)] = s;
  }

  // TODO fix generalize_predecessor for IC3CAR
  //      might need to override it
  //      behaves a bit differently with both concrete and abstract next state
  //      vars
  if (options_.ic3_pregen_) {
    logger.log(1,
               "WARNING automatically disabling predecessor generalization -- "
               "not supported in IC3CAR yet.");
    options_.ic3_pregen_ = false;
  }
}

ProverResult IC3CAR::step_0()
{
  // initially reach_k == -1
  assert(reached_k_ < 0);
  logger.log(1, "Checking if initial states satisfy property");

  push_solver_context();  // create a context for this solving procedure
  solver_->assert_formula(ts_.init());
  logger.log(3, "push init: {}", ts_.init());
  solver_->assert_formula(bad_);
  logger.log(3, "push bad: {}", bad_);
  Result r = check_sat();
  if (r.is_sat()) {
    pop_solver_context();
    // trace is only one bad state that intersects with initial
    cex_.clear();
    cex_.push_back(bad_);
    return ProverResult::FALSE;
  } else {
    assert(r.is_unsat());
    reached_k_ = 0;  // keep reached_k_ aligned with number of frames
  }
  pop_solver_context();
  // end of I /\ bad
  push_solver_context();  // create a context for this solving procedure
  //  solver_->assert_formula(init_label_);
  // logger.log(3, "push init: {}", init_label_);
  assert_trans_label();
  logger.log(3, "push trans: {}", trans_label_);
  solver_->assert_formula(ts_.next(bad_));
  logger.log(3, "push next bad: {}", ts_.next(bad_));
  // end of T /\ bad'

  ProverResult pres = ProverResult::UNKNOWN;
  r = check_sat();
  if (r.is_unsat()) {
    pres = ProverResult::TRUE;
  }
  pop_solver_context();

  return pres;
}

void IC3CAR::push_frame() {}

void IC3CAR::successor_generalization_and_fix(size_t i,
                                              const Term & c,
                                              IC3Formula & pred)
{
  logger.log(3, "succ_and_fix: {}, {}, {}", i, c, pred.term);
  TermVec orig_pred_children;
  if (approx_pregen_) {
    assert(!pred.disjunction);
    // save original predecessor conjuncts
    orig_pred_children = pred.children;
    assert(orig_pred_children.size());
  }

  predecessor_generalization(i, c, pred);  // no implementation by default

  logger.log(3, "approx_pregen_: {}", approx_pregen_);

  // if (approx_pregen_ && i >= 1) {
  TermVec dropped;
  assert(orig_pred_children.size());
  TermVec pred_children = pred.children;
  UnorderedTermSet reduced_pred_children(pred_children.begin(),
                                         pred_children.end());
  for (const auto & cc : orig_pred_children) {
    if (reduced_pred_children.find(cc) == reduced_pred_children.end()) {
      dropped.push_back(cc);
    }
  }
  // if predecessor generalization is approximate
  // need to make sure it does not intersect with F[i-2]
  // Term formula = frame_labels_[i]; // redudant
  // formula = solver_->make_term(And, formula, pred.term);
  // bool unsat =
  //    reducer_.reduce_assump_unsatcore(formula, dropped, pred_children);
  // assert(unsat);
  pred = ic3formula_conjunction(pred_children);
  //}

  assert(pred.term);
  assert(pred.children.size());
  assert(!pred.disjunction);  // expecting a conjunction
}

bool IC3CAR::rel_ind_check(size_t i,
                           const IC3Formula & s,
                           IC3Formula & out,
                           bool get_pred)
{
  assert(i >= 0);
  assert(i < frames_.size());
  // expecting to be the polarity for proof goals, not frames
  // e.g. a conjunction
  assert(!s.disjunction);

  assert(solver_context_ == 0);
  push_solver_context();

  // add O'[i]
  // assert frame labels
  {
    // solver_->assert_formula(next_bad_label_); // add next bad
    //  we now obtain the O'_l
    solver_->assert_formula(get_frame_formula(i));
  }
  // add s
  solver_->assert_formula(s.term);
  // add Trans
  assert_trans_label();
  logger.log(1, "assert trans label");
  // solver_->assert_formula(ts_.trans());
  // use assumptions for c' so we can get cheap initial
  // generalization if the check is unsat

  // NOTE: relying on same order between assumps_ and c.children
  assumps_.clear();
  // Obtain the literal form of the state s
  {
    // TODO shuffle assumps and (a copy of) c.children
    //      if random seed is set
    logger.log(3, "current s is : {}", s.term);
    Term lbl;
    for (const auto & cc : s.children) {
      lbl = label(cc);
      if (lbl != cc && !is_global_label(lbl)) {
        // only need to add assertion if the label is not the same as ccnext
        // could be the same if ccnext is already a literal
        // and is not already in a global assumption
        solver_->assert_formula(solver_->make_term(Implies, lbl, cc));
      }
      assumps_.push_back(lbl);
      logger.log(3, "add new lbl to assumps: {}, {}", lbl, cc);
    }
  }

  Result r = check_sat_assuming(assumps_);
  if (r.is_sat()) {
    out = get_model_ic3formula();
    if (get_pred) {
      // need to obtain the value for the next state variables
      logger.log(3, "sat new proof goal: {}", out.term);
      if (options_.ic3_pregen_) {
        successor_generalization_and_fix(i, s.term, out);
        assert(out.term);
        assert(out.children.size());
        assert(!out.disjunction);  // expecting a conjunction
      }
    }
    assert(ic3formula_check_valid(out));
  } else {
    assert(r.is_unsat());  // not expecting to get unknown
    logger.log(3, "unsat and obtain core: {}", r.is_unsat());
    // Use unsat core to get cheap generalization
    // TODO Obtain minimal unsat core
    UnorderedTermSet core;
    solver_->get_unsat_assumptions(core);
    assert(core.size());

    TermVec gen;  // cheap unsat-core generalization of c
    TermVec rem;  // conjuncts removed by unsat core
    // might need to be re-added if it
    // ends up intersecting with initial
    assert(assumps_.size() == s.children.size());
    for (size_t i = 0; i < assumps_.size(); ++i) {
      if (core.find(assumps_.at(i)) == core.end()) {
        rem.push_back(s.children.at(i));
        logger.log(
            3, "not in unsat core: {}, {}", assumps_.at(i), s.children.at(i));
      } else {
        gen.push_back(s.children.at(i));
        logger.log(
            3, "in unsat core: {}, {}", assumps_.at(i), s.children.at(i));
      }
    }

    // DO WE NEED THIS?
    // fix_if_intersects_initial(gen, rem);
    assert(gen.size() >= core.size());
    TermVec ngen;
    for (Term c : gen) {
      ngen.push_back(ts_.next(c));
    }
    // keep it as a conjunction for now
    out = ic3formula_conjunction(ngen);
    logger.log(3, "generalized c: {}", out.term);
  }
  // else {
  //  assert(r.is_unsat());  // not expecting to get unknown
  // don't generalize with an unsat core, just keep c
  //  out = s;
  //  logger.log(3, "No generalize only keep c: {}", c.term);
  //}

  pop_solver_context();
  assert(!solver_context_);

  if (r.is_sat() && get_pred) {
    assert(out.term);
    assert(out.children.size());

    // this check needs to be here after the solver context has been popped
    // if i == 1 and there's a predecessor, then it should be an initial state
    assert(i != 1 || check_intersects_initial(out.term));

    // should never intersect with a frame before F[i-1]
    // otherwise, this predecessor should have been found
    // in a previous step (before a new frame was pushed)
    // assert(i < 2 || !check_intersects(out.term, get_frame_term(i - 2)));
  }

  assert(!r.is_unknown());
  return r.is_sat();
}

void IC3CAR::add_to_under_frame(IC3Formula & t, int j)
{
  // j must exists
  assert(j - 1 < under_frames_.size());
  if (j >= under_frames_.size()) {
    under_frames_.push_back({});
  }
  logger.log(3, "add to under_frame: u[{}] = {}", (j), t.term);
  under_frames_[j].push_back(t);
}

void IC3CAR::construct_trace(const ProofGoal * pg, TermVec & out, int j)
{
  assert(!solver_context_);
  assert(pg);
  assert(pg->target.term);
  assert(check_intersects_initial(pg->target.term));

  out.clear();

  // out.push_back(bad_); //we need to
  while (pg) {
    logger.log(3, "cex: {}, {}", pg->target.term, pg->idx);
    out.push_back(pg->target.term);
    assert(ts_.only_curr(out.back()));
    pg = pg->next;
    j--;
  }
  // add the initial state? or we need track U-sequence
  // current one is in U[j]

  logger.log(3, "current under_frame at {}", j);

  if (j >= 0) {
    while (j > 0) {
      Term curr_frame = solver_->make_term(false);
      for (IC3Formula & c : under_frames_[j]) {
        curr_frame = solver_->make_term(Or, curr_frame, c.term);
      }
      logger.log(3, "current under_frame U[{}] = {}", j, curr_frame);
      out.push_back(curr_frame);
      j--;
    }
    logger.log(3, "init under frame U[0] = {}", under_frames_[0].size());
    out.push_back(ts_.init());
  }

  std::reverse(out.begin(), out.end());
}

// last overlaps with bad and fist with initial
bool IC3CAR::is_cex_valid(smt::TermVec & out)
{
  assert(out.size() >= 2);
  push_solver_context();
  solver_->assert_formula(solver_->make_term(And, ts_.init(), out.at(0)));
  Result r = check_sat();
  if (r.is_unsat()) {
    logger.log(1, "Not intersects with init");
    return false;
  }
  pop_solver_context();
  push_solver_context();
  solver_->assert_formula(bad_label_);
  solver_->assert_formula(out.back());
  r = check_sat();
  if (r.is_unsat()) {
    logger.log(1, "Not intersects with bad");
    return false;
  }
  pop_solver_context();
  return true;
}

bool IC3CAR::is_blocked(ProofGoalQueue & proof_goals,
                        int j,
                        std::vector<IC3Formula> & frame_tmp)
{
  logger.log(3, "current s is from U[{}]", j);
  while (!proof_goals.empty()) {
    const ProofGoal * pg = proof_goals.top();
    IC3Formula s = pg->target;
    size_t l = pg->idx - 1;  // by default we pass l + 1 for the goal
    logger.log(3,
               "proof goal: (s = {}, l = {})",
               pg->target.term,
               ((int)(pg->idx) - 1));
    // 1. check whether it has been traced back to initial
    if (pg->idx <= 0) {
      // went all the way back to bad, we need to trace back to initial
      construct_trace(pg, cex_, j);
      // since the first cex is at bad
      if (!is_cex_valid(cex_)) {
        logger.log(1, "Counterexample is wrong");
        exit(-1);
      }
      // in case this is spurious, clear the queue of proof goals
      // which might not have been precise
      // TODO might have to change this if there's an algorithm
      // that refines but can keep proof goals around
      proof_goals.clear();

      return false;
    }

    // 2. IsSATAssuming(s, T/\O'_l)
    IC3Formula out;
    if (rel_ind_check(l, pg->target, out)) {
      // t(1) = getModel|primed_version
      TermVec conjuncts;
      for (const auto & c : out.children) {
        conjuncts.push_back(ts_.curr(c));
      }
      IC3Formula t = ic3formula_conjunction(conjuncts);
      add_to_under_frame(t, j + 1);  // add to U[j + 1]
      j++;
      // Extending U
      // stack.push(t, l-1)
      logger.log(3, "add new proof goal: ({}, {})", t.term, (((int)l) - 1));
      proof_goals.new_proof_goal(
          t, l, pg);  // need to remove t from O[l-1], pass l -1 + 1
    } else {
      // stack.pop()
      proof_goals.pop();
      // uc := GetUnsatCore()
      // extending Over and Otmp. already it is current version
      // Unsat core is already in primed version and literals
      logger.log(3,
                 "UNSAT, check l+1 < {}: {} ",
                 frames_.size(),
                 (l + 1 < frames_.size()));
      if (l + 1 < frames_.size()) {
        frames_[l + 1].push_back(
            out);  // add not uc, here we store cubes only in frames
        // add (s, l+1) to stack
        // similar IC3 query O'[l+1] /\ !s' /\ T /\ s
        // here we have used the unsat core
        proof_goals.new_proof_goal(
            s, l + 2);  // no need for store the predecessor, pass (l + 1) + 1
      } else {
        // we need to add a new frontier
        frame_tmp.push_back(out);
      }
    }
  }
  // check whether we have reached a fixed point
  return true;
}

int IC3CAR::pick_state(IC3Formula & out, int & idx)
{
  if (under_frames_.size() == 1) {
    TermVec inits;
    solver_->push();
    solver_->assert_formula(ts_.next(ts_.init()));
    Result r = solver_->check_sat();
    assert(r.is_sat());
    // inits.push_back(ts_.init());
    out = get_model_ic3formula();
    solver_->pop();
    for (Term t : out.children) {
      inits.push_back(ts_.curr(t));
    }
    out = ic3formula_conjunction(inits);
    logger.log(3, "Pick a state s: {}", out.term);
    return 0;
  }
  // currently return the state in largest under approximation frame
  size_t frame_idx = under_frames_.size() - 1;
  std::random_device rd;   // obtain a random number from hardware
  std::mt19937 gen(rd());  // seed the generator
  std::uniform_int_distribution<> distr(
      0, under_frames_[frame_idx].size() - 1);  // define the range
  int tmp_idx = distr(gen);
  if (idx >= 0 && idx < under_frames_[frame_idx].size()) {
    out = under_frames_[frame_idx][idx];
    idx++;
  } else {
    out = under_frames_[frame_idx][tmp_idx];
    idx = tmp_idx;
  }

  return frame_idx;
}

Term IC3CAR::get_frame_formula(int frame_idx)
{
  assert(frame_idx < frames_.size());
  if (frame_idx == 0) {
    return ts_.next(bad_);
  }
  Term cnf = solver_->make_term(true);  // by default
  for (IC3Formula & terms : frames_[frame_idx]) {
    // all IC3Formula is a conjunction of predicates
    IC3Formula negated_formula = ic3formula_negate(terms);
    cnf = solver_->make_term(And, cnf, negated_formula.term);
  }
  logger.log(3, "over frame formula: {}", cnf);
  return cnf;
}

bool IC3CAR::reach_fixed_point()
{
  if (frames_.size() <= 2) {
    return false;
  }
  assert(frames_.size() > 1);
  Term disjuncts = get_frame_formula(0);
  disjuncts = solver_->make_term(Or, disjuncts, get_frame_formula(1));
  for (int i = 2; i < frames_.size(); i++) {
    Term curr_frame = get_frame_formula(i);
    solver_->push();
    // solver_->assert_formula(solver_->make_term(Not, bad_label_));
    // solver_->assert_formula(solver_->make_term(Not, trans_label_));
    solver_->assert_formula(solver_->make_term(
        And, solver_->make_term(Not, disjuncts), curr_frame));
    logger.log(
        3, "check !disj formula: {}", solver_->make_term(Not, disjuncts));
    logger.log(3,
               "check fixedpoint formula: {}",
               solver_->make_term(
                   And, solver_->make_term(Not, disjuncts), curr_frame));
    Result r = check_sat();
    bool reached = r.is_unsat();
    logger.log(1, "formula unsat? {}", reached);
    solver_->pop();
    if (reached) {
      return true;
    }
    // continue to add formulas
    disjuncts = solver_->make_term(Or, disjuncts, curr_frame);
  }
  return false;
}

// backward CAR: either return a counterexample or conclude the abstract system
// is safe
ProverResult IC3CAR::step(int i)
{
  // at first, i = 0, reached_k_ = -1
  if (i <= reached_k_) {
    return ProverResult::UNKNOWN;
  }

  if (reached_k_ < 0) {  // current k = -1
    return step_0();     // step 0 and 1, 0: init & bad
  }

  // reached_k_ is the number of transitions that have been checked
  // at this point there are reached_k_ + 1 frames that don't
  // intersect init, and reached_k_ + 2 frames overall
  assert(reached_k_ == frontier_idx());
  logger.log(1, "Current frame size: {}", frames_.size());
  logger.log(1, "Blocking phase at frame {}", i);
  // set the first to be !P

  int cube_idx = 0; // the cube in the frontier
  // 1. first pick a state from the U
  // int level = under_frames_.size() - 1;
  IC3Formula goal;
  int j = pick_state(goal, cube_idx);

  // 2. O_tmp = not P
  // Term prop = smart_not(bad_);  // must be a predicate?
  std::vector<IC3Formula> frame_tmp; // initially it is true
  // frame_tmp.push_back();

  ProofGoalQueue proof_goals;
  // int frame_level = frames_.size() - 1;
  //  we need to have the
  proof_goals.new_proof_goal(goal, frames_.size(), nullptr);

  bool blocked = is_blocked(proof_goals, j, frame_tmp);

  if (!blocked) {
    return ProverResult::FALSE;
  } else {
    // now we can check fixed point
    if (reach_fixed_point()) {
      return ProverResult::TRUE;
    }
    // we need to push forward the over-approximate sets
    frames_.push_back(frame_tmp);
    logger.log(3,
               "added new frame[{}]: {}",
               (frames_.size() - 1),
               get_frame_formula(frames_.size() - 1));
  }

  reset_solver();

  ++reached_k_;

  return ProverResult::UNKNOWN;
}

ProverResult IC3CAR::check_until(int k)
{
  initialize();
  // make sure derived class implemented initialize and called
  // this version of initialize with super::initialize or
  // (for experts only) set the initialized_ flag without
  // ever initializing base classes
  assert(initialized_);

  ProverResult res;

  RefineResult ref_res;
  int i = reached_k_ + 1;  // value should be zero now, i = 0
  assert(reached_k_ + 1 >= 0);

  frames_.push_back({});  // we set O[0] = !P

  while (i <= k) {
    res = step(i);

    if (res == ProverResult::FALSE) {
      assert(cex_.size());
      RefineResult s = refine();
      if (s == REFINE_SUCCESS) {
        // we need to clear the under frames
        under_frames_.clear();
        push_under_frame(); // set the U[0] = I
        continue;
      } else if (s == REFINE_NONE) {
        // this is a real counterexample
        assert(cex_.size());
        logger.log(3, "The counterexample has lengh of {}", cex_.size());
        return ProverResult::FALSE;
      } else {
        assert(s == REFINE_FAIL);
        logger.log(1, "IC3CAR: refinement failure, returning unknown");
        return ProverResult::UNKNOWN;
      }
    } else {
      ++i;
    }

    if (res != ProverResult::UNKNOWN) {
      return res;
    }
  }

  return ProverResult::UNKNOWN;
}

void IC3CAR::abstract()
{
  const UnorderedTermSet & bool_symbols =
      ia_.do_abstraction();  // create v.next <-> v.next^ values, and replace
                             // trans with new abstract ones
  // the set of boolean varibles present in system is returned

  // don't add boolean symbols that are never used in the system
  // this is an optimization and a fix for some options
  // if using mathsat with bool_model_generation
  // it will fail to get the value of symbols that don't
  // appear in the query
  // thus we don't include those symbols in our cubes
  UnorderedTermSet used_symbols;
  get_free_symbolic_consts(ts_.init(), used_symbols);
  get_free_symbolic_consts(ts_.trans(), used_symbols);
  get_free_symbolic_consts(bad_, used_symbols);

  // add predicates automatically added by ia_
  // to our predset_
  // needed to prevent adding duplicate predicates later
  for (const auto & sym : bool_symbols) {
    assert(sym->is_symbolic_const());
    if (used_symbols.find(sym) != used_symbols.end()) {
      add_predicate(sym);
    }
  }

  assert(ts_.init());  // should be non-null
  assert(ts_.trans());
}
// refine the abstraction by cex
RefineResult IC3CAR::refine()
{
  // counterexample trace should have been populated
  assert(cex_.size());
  if (cex_.size() == 1) {
    // if there are no transitions, then this is a concrete CEX
    return REFINE_NONE;
  }

  size_t cex_length = cex_.size();

  // use interpolator to get predicates
  // remember -- need to transfer between solvers
  assert(interpolator_);

  TermVec formulae;
  for (size_t i = 0; i < cex_length; ++i) {
    // make sure to_solver_ cache is populated with unrolled symbols
    register_symbol_mappings(i);

    Term t = unroller_.at_time(cex_[i], i);
    if (i + 1 < cex_length) {
      t = solver_->make_term(And, t, unroller_.at_time(conc_ts_.trans(), i));
    }
    logger.log(3, "refine() cex {} : {}", i, t);
    formulae.push_back(to_interpolator_.transfer_term(t, BOOL));
  }

  TermVec out_interpolants;
  Result r =
      interpolator_->get_sequence_interpolants(formulae, out_interpolants);

  if (r.is_sat()) {
    // this is a real counterexample, so the property is false
    return RefineResult::REFINE_NONE;
  }

  // record the length of this counterexample
  // important to set it here because it's used in register_symbol_mapping
  // to determine if state variables unrolled to a certain length
  // have already been cached in to_solver_
  longest_cex_length_ = cex_length;

  UnorderedTermSet preds;
  for (auto const & I : out_interpolants) {
    if (!I) {
      assert(
          r.is_unknown());  // should only have null terms if got unknown result
      continue;
    }

    Term solver_I = unroller_.untime(to_solver_.transfer_term(I, BOOL));
    assert(conc_ts_.only_curr(solver_I));
    logger.log(3, "got interpolant: {}", solver_I);
    get_predicates(solver_, solver_I, preds, false, false, true);
  }

  // new predicates
  TermVec fresh_preds;
  for (auto const & p : preds) {
    if (predset_.find(p) == predset_.end()) {
      // unseen predicate
      fresh_preds.push_back(p);
    }
  }

  if (!fresh_preds.size()) {
    logger.log(1, "IC3CAR: refinement failed couldn't find any new predicates");
    return RefineResult::REFINE_FAIL;
  }

  if (options_.random_seed_ > 0) {
    shuffle(fresh_preds.begin(),
            fresh_preds.end(),
            default_random_engine(options_.random_seed_));
  }

  // reduce new predicates
  TermVec red_preds;
  if (options_.ic3ia_reduce_preds_
      && ia_.reduce_predicates(cex_, fresh_preds, red_preds)) {
    // reduction successful
    logger.log(2,
               "reduce predicates successful {}/{}",
               red_preds.size(),
               fresh_preds.size());
    if (red_preds.size() < fresh_preds.size()) {
      fresh_preds.clear();
      fresh_preds.insert(fresh_preds.end(), red_preds.begin(), red_preds.end());
    }
  } else {
    // if enabled should only fail if removed all predicates
    // this can happen when there are uninterpreted functions
    // the unrolling can force incompatible UF interpretations
    // but IC3 (which doesn't unroll) still needs the predicates
    // in this case, just use all the fresh predicates
    assert(!options_.ic3ia_reduce_preds_ || red_preds.size() == 0);
    logger.log(2, "reduce predicates FAILED");
  }

  // add all the new predicates
  for (auto const & p : fresh_preds) {
    bool new_pred = add_predicate(p);
    // expect all predicates to be new (e.g. unseen)
    // they were already filtered above
    assert(new_pred);
  }

  logger.log(1, "{} new predicates added by refinement", fresh_preds.size());

  // able to refine the system to rule out this abstract counterexample
  return RefineResult::REFINE_SUCCESS;
}

void IC3CAR::reset_solver()
{
  super::reset_solver();

  for (const auto & elem : lbl2pred_) {
    solver_->assert_formula(solver_->make_term(Equal, elem.first, elem.second));
    Term npred = ts_.next(elem.second);
    Term nlbl = label(npred);
    solver_->assert_formula(solver_->make_term(Equal, nlbl, npred));
  }
}

bool IC3CAR::is_global_label(const Term & l) const
{
  // all labels used by IC3CAR should be globally assumed
  // the assertion will check that this assumption holds though
  assert(super::is_global_label(l) || all_lbls_.find(l) != all_lbls_.end());
  return true;
}

void IC3CAR::reabstract()
{
  // don't add boolean symbols that are never used in the system
  // this is an optimization and a fix for some options
  // if using mathsat with bool_model_generation
  // it will fail to get the value of symbols that don't
  // appear in the query
  // thus we don't include those symbols in our cubes
  UnorderedTermSet used_symbols;
  get_free_symbolic_consts(ts_.init(), used_symbols);
  get_free_symbolic_consts(ts_.trans(), used_symbols);
  get_free_symbolic_consts(bad_, used_symbols);

  UnorderedTermSet preds;
  // reset init and trans -- done with calling ia_.do_abstraction
  // then add all boolean constants as (precise) predicates
  for (const auto & p : ia_.do_abstraction()) {
    assert(p->is_symbolic_const());
    if (used_symbols.find(p) != used_symbols.end()) {
      preds.insert(p);
    }
  }

  // predicates from init and bad
  get_predicates(solver_, ts_.init(), preds, false, false, true);
  get_predicates(solver_, bad_, preds, false, false, true);
  // instead of add previously found predicates, we add all the predicates in
  // frame 1
  get_predicates(solver_, get_frame_term(1), preds, false, false, true);

  super::reset_solver();
  if (failed_to_reset_solver_) {
    throw PonoException(
        "IC3CAR::reabstract Cannot reabstract because "
        "the underlying SMT solver doesn't support "
        "the reset-solver method");
  }
  predset_.clear();
  predlbls_.clear();

  // add predicates
  for (const auto & p : preds) {
    add_predicate(p);
  }
}

bool IC3CAR::add_predicate(const Term & pred)
{
  if (predset_.find(pred) != predset_.end()) {
    // don't allow re-adding the same predicate
    return false;
  }

  assert(ts_.only_curr(pred));
  logger.log(2, "adding predicate {}", pred);
  predset_.insert(pred);
  assert(pred->get_sort() == boolsort_);
  assert(pred->is_symbolic_const() || is_predicate(pred, boolsort_));

  Term lbl = label(pred);  // create boolean symbol for the predicate
  // set the negated label as well
  // can use in either polarity because we add a bi-implication
  labels_[solver_->make_term(Not, pred)] = solver_->make_term(Not, lbl);

  predlbls_.insert(lbl);  // predicate bool symbols
  lbl2pred_[lbl] = pred;  // bool to pred

  Term npred = ts_.next(pred);  // next time version of the predicate
  Term nlbl = label(npred);
  lbl2nlbl_[lbl] = nlbl;  // current to next bools
  nlbl2npred_[nlbl] = npred;

  labels_[solver_->make_term(Not, npred)] = solver_->make_term(Not, nlbl);

  if (!pred->is_symbolic_const()) {
    // only need to assert equalities for labels that are distinct
    assert(lbl != pred);
    solver_->assert_formula(solver_->make_term(Equal, lbl, pred));
    logger.log(
        3, "adding predicate equals {}", solver_->make_term(Equal, lbl, pred));
    solver_->assert_formula(solver_->make_term(Equal, nlbl, npred));
    logger.log(3,
               "adding next predicate equals {}",
               solver_->make_term(Equal, nlbl, npred));

    // only need to modify transition relation for non constants
    // boolean constants will be precise

    // add predicate to abstraction and get the new constraint
    Term predabs_rel = ia_.predicate_refinement(pred);
    static_cast<RelationalTransitionSystem &>(ts_).constrain_trans(predabs_rel);
    // refine the transition relation incrementally
    // by adding a new constraint
    assert(!solver_context_);  // should be at context 0
    solver_->assert_formula(
        solver_->make_term(Implies, trans_label_, predabs_rel));
    logger.log(3,
               "adding predicate equals {}",
               solver_->make_term(Implies, trans_label_, predabs_rel));
  }

  // keep track of the labels and different polarities for debugging assertions
  all_lbls_.insert(lbl);
  all_lbls_.insert(solver_->make_term(Not, lbl));
  all_lbls_.insert(nlbl);
  all_lbls_.insert(solver_->make_term(Not, nlbl));

  return true;
}

void IC3CAR::register_symbol_mappings(size_t i)
{
  if (i < longest_cex_length_) {
    // these symbols should have already been handled
  }

  UnorderedTermMap & cache = to_solver_.get_cache();
  Term unrolled_sv;
  for (const auto & sv : ts_.statevars()) {
    unrolled_sv = unroller_.at_time(sv, i);
    cache[to_interpolator_.transfer_term(unrolled_sv)] = unrolled_sv;
  }
}

}  // namespace pono
