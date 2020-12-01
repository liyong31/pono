/*********************                                                  */
/*! \file ic3.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bit-level IC3 implementation using the IC3Base abstract base class
**/

#pragma once

#include <unordered_map>
#include <unordered_set>

#include "engines/ic3base.h"

namespace pono {

class ClauseHandler : public IC3UnitHandler
{
 public:
  ClauseHandler(const smt::SmtSolver & s) : IC3UnitHandler(s) {}

  IC3Unit create(const smt::TermVec & c) const override;

  IC3Unit negate(const IC3Unit & u) const override;

  bool check_valid(const IC3Unit & u) const override;
};

}  // namespace pono
