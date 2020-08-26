/*********************                                                        */
/*! \file cegar.h
** \verbatim
** Top contributors (to current version):
**   Ahmed Irfan, Makai Mann
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief An abstract base class for Counter-Example Guided Abstraction
*Refinement
**        (CEGAR) techniques.
**
**/

#pragma once

#include "engines/prover.h"

namespace pono {

class CEGAR : public Prover
{
  typedef Prover super;

 public:
  CEGAR(const Property & p, smt::SolverEnum se) : super(p, se) { initialize(); }
  CEGAR(const Property & p, const smt::SmtSolver & solver) : super(p, solver)
  {
    initialize();
  }
  CEGAR(const PonoOptions & opt, const Property & p, smt::SolverEnum se)
      : super(opt, p, se)
  {
    initialize();
  }
  CEGAR(const PonoOptions & opt,
        const Property & p,
        const smt::SmtSolver & solver)
      : super(opt, p, solver)
  {
    initialize();
  }
  virtual ~CEGAR(){};

  void initialize() override
  {
    super::initialize();
    // abstract the transition system
    abstract();
  }

 protected:
  /** Abstract the transition system -- usually only performed once
   *  (in initialize)
   */
  virtual void abstract() = 0;
  /** Refine the abstracted transition system
   *  Typically performed a refinement loop
   */
  virtual void refine() = 0;
};

}  // namespace pono
