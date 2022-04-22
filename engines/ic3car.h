/*********************                                                  */
/*! \file ic3car.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan, Yong Li
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief IC3 via Implicit Predicate Abstraction (IC3CAR) implementation
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

#pragma once

#include "engines/ic3.h"
#include "modifiers/implicit_predicate_abstractor.h"
#include "smt-switch/term_translator.h"

namespace pono {

using UnorderedTermLevelMap = std::unordered_map<smt::Term, std::pair<smt::Term, int>>;

class IC3CAR : public IC3
{
 public:
  // itp_se is the SolverEnum for the interpolator

  IC3CAR(const Property & p,
        const TransitionSystem & ts,
        const smt::SmtSolver & s,
        PonoOptions opt = PonoOptions());

  virtual ~IC3CAR() {}

  typedef IC3 super;

  void add_important_var(smt::Term v);

 protected:
  // Note: important that conc_ts_ and abs_ts_ are before ia_
  //       because we will pass them to ia_ and they must be
  //       be initialized first

  TransitionSystem conc_ts_;

  ImplicitPredicateAbstractor ia_;

  smt::UnorderedTermSet predset_;  ///< set of current predicates
  // useful for checking if predicate has been added already
  // also available as a vector in ia_.predicates()

  smt::SmtSolver interpolator_;  ///< interpolator for refinement
  smt::TermTranslator
      to_interpolator_;  ///< transfer terms from solver_ to interpolator_
  smt::TermTranslator
      to_solver_;  ///< transfer terms from interpolator_ to solver_

  size_t longest_cex_length_;  ///< keeps track of longest (abstract)
                               ///< counterexample

  ///< the under-approximate data structure.
  ///< a vector of the given Unit template
  ///< which changes depending on the implementation
  std::vector<std::vector<IC3Formula>> under_frames_;
//   smt::TermVec under_frame_labels_;  ///< labels to activate under frames

  // label for next bad
  smt::Term next_bad_label_;

  // Since MathSAT is the best solver for IC3CAR it helps to use
  // its bool_model_generation option which doesn't enable
  // model generation for theories
  // instead, we assign indicator labels to check the value of
  // predicates. This should still work fine with other solvers
  smt::UnorderedTermMap lbl2pred_;
  smt::UnorderedTermSet predlbls_;
  smt::UnorderedTermMap lbl2nlbl_;
  smt::UnorderedTermMap nlbl2npred_;
  smt::UnorderedTermSet all_lbls_;  ///< for debugging assertions only
                                    ///< keeps track of both polarities
                                    ///< mostly needed because some solvers
                                    ///< do automatic top-level propagation
                                    ///< which means you can't count on a symbol
                                    ///< staying a symbol
  UnorderedTermLevelMap term2level_;

  /** Overriding the method. This will return the concrete_ts_ because ts_ is an
   *  abstraction of concrete_ts_.
   */
  TransitionSystem & prover_interface_ts() override { return conc_ts_; };
  // pure virtual method implementations

  IC3Formula get_model_ic3formula() const override;

  bool ic3formula_check_valid(const IC3Formula & u) const override;

  // need to override this because IC3CAR is not as restricted as
  // (bit-level) IC3
  void check_ts() const override;

  void initialize() override;

  void abstract() override;

  RefineResult refine() override;

  void push_under_frame();

  void reset_solver() override;

  bool is_global_label(const smt::Term & l) const override;

  // specific to IC3CAR

  void reabstract();

  /** Adds predicate to abstraction
   *  (calls ia_.add_predicate)
   *  and declares a new predicate state var (in pred_statevars_)
   *  @param pred the predicate over current state variables
   *  @return true iff the predicate was new (not seen before)
   */
  bool add_predicate(const smt::Term & pred);

  /** Register a state variable mapping in to_solver_
   *  This is a bit ugly but it's needed because symbols aren't created in
   * to_solver_ so it needs the mapping from interpolator_ symbols to solver_
   * symbols
   *  TODO look into a cleaner solution
   *  @param i the unrolling for state variables
   *         makes sure not to repeat work
   */
  void register_symbol_mappings(size_t i);

  ProverResult step_0();

  virtual void push_frame();

  void push_over_frontier();

  //virtual ProverResult step(int i);

  virtual ProverResult check_until(int k);

  bool is_blocked(ProofGoalQueue& proof_goals, int j
                , std::vector<IC3Formula>& frame_tmp);


  void add_to_under_frame(IC3Formula& t, int j );

  virtual bool rel_ind_check(size_t i,
                            const IC3Formula & c,
                            IC3Formula & out,
                            bool get_pred = true);

  int pick_state(IC3Formula& out, int& idx);

  void successor_generalization_and_fix(size_t i, const smt::Term & c,
                                                 IC3Formula & pred);
  smt::Term get_frame_formula(int frame_idx);

  bool reach_fixed_point();

  void construct_trace(const ProofGoal * pg, smt::TermVec & out, const UnorderedTermLevelMap& term2level);

  // last overlaps with bad and fist with initial
  bool is_cex_valid(smt::TermVec & out);

  virtual ProverResult step(int i);

  bool is_connected(const smt::Term& curr, const smt::Term& succ);

  void abstract_cube(const IC3Formula& cube, smt::Term& out);


  

};

}  // namespace pono
