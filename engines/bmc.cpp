/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Makai Mann
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "bmc.h"
#include "utils/logger.h"

using namespace smt;

namespace pono {

Bmc::Bmc(const Property & p, const TransitionSystem & ts,
         const SmtSolver & solver, PonoOptions opt)
  : super(p, ts, solver, opt)
{
  engine_ = Engine::BMC;
}

Bmc::~Bmc() {}

void Bmc::initialize()
{
  if (initialized_) {
    return;
  }

  super::initialize();

  // NOTE: There's an implicit assumption that this solver is only used for
  // model checking once Otherwise there could be conflicting assertions to
  // the solver or it could just be polluted with redundant assertions in the
  // future we can use solver_->reset_assertions(), but it is not currently
  // supported in boolector
  solver_->assert_formula(unroller_.at_time(ts_.init(), 0));
}

ProverResult Bmc::check_until(int k)
{
  // even before initialization
  // we randomly sample a path from the system
  if (options_.bmc_sampling_ && !sample_path(k)) {
    //compute_witness();
    return ProverResult::FALSE;
  }else if (options_.bmc_sampling_){
    return ProverResult::UNKNOWN;
  }

  initialize();

  for (int i = reached_k_ + 1; i <= k; ++i) {
    if (!step(i)) {
      compute_witness();
      return ProverResult::FALSE;
    }
  }
  return ProverResult::UNKNOWN;
}

Term Bmc::obtain_model_values(UnorderedTermMap & map, bool next)
{
    //witness_.push_back(UnorderedTermMap());
    //UnorderedTermMap & map = witness_.back();
    logger.log(2, "obtain state: {}", next);
    Term state = solver_->make_term(true);
    //logger.log(1, "trabs var: {}", ts_.trans());
    for (const auto &v : ts_.statevars()) {
      const Term &vi = next ? ts_.next(v) : v;
      //logger.log(1, "state var: {}", vi);
      const Term &r = solver_->get_value(vi);
      //logger.log(1, "state value: {}", r);
      map[v] = r;
      state = solver_->make_term(And, state, solver_->make_term(Equal, v, r));
      //logger.log(1, "returned state: {}", state);
    }

    return state;
}

bool Bmc::sample_path(int k) 
{
  // by default, solver is empty now
  if (!ts_.only_curr(bad_)) {
    throw PonoException("Property should not contain inputs or next state variables");
  }

  Term curr = ts_.init();
  //Term next_bad = ts_.next(bad_);
  Term visited = solver_->make_term(true);

  for (int i = 0; i <= k; i ++) {
    witness_.push_back(UnorderedTermMap());
    UnorderedTermMap & map = witness_.back();
    solver_->push();
    logger.log(1, "Sampling state at bound: {} ", i);
    solver_->assert_formula(curr);
    solver_->assert_formula(bad_);
    Result r = solver_->check_sat();
    if (r.is_sat()) {
      if (i == 0) {
        obtain_model_values(map, false);
      }// else this state is already been put in witness_
      solver_->pop();
      return false;
    } else {
      solver_->pop();
      //logger.log(2, "Sampling next state");
      // next state should not be the current one, and it is universal
      visited = solver_->make_term(And, visited, solver_->make_term(Not, ts_.next(curr)));
      solver_->assert_formula(visited);
      solver_->push();
      // we need to sample next state
      solver_->assert_formula(curr);
      solver_->assert_formula(ts_.trans());
      r = solver_->check_sat();
      if (! r.is_sat()) {
        // path discontinued
        solver_->pop();
        witness_.clear();
        return true;
      }

      // obtain the next state
      if (i == 0) {
        // we need to put the current state as well
        obtain_model_values(map, false);
        witness_.push_back(UnorderedTermMap()); // add next state now
        //map = witness_.back();
      }
      // put the next states
      curr = obtain_model_values(witness_.back(), true);
      solver_->pop();
    }
  }
  
  witness_.clear();
  return true;
}

bool Bmc::step(int i)
{
  if (i <= reached_k_) {
    return true;
  }

  bool res = true;
  if (i > 0) {
    solver_->assert_formula(unroller_.at_time(ts_.trans(), i - 1));
  }

  solver_->push();
  logger.log(1, "Checking bmc at bound: {}", i);
  solver_->assert_formula(unroller_.at_time(bad_, i));
  Result r = solver_->check_sat();
  if (r.is_sat()) {
    res = false;
  } else {
    solver_->pop();
    ++reached_k_;
  }

  return res;
}

}  // namespace pono
