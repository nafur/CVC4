/*********************                                                        */
/*! \file statistics.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/statistics.h"

#include "util/safe_print.h"
#include "util/statistics_registry.h" // for details about class Stat

namespace cvc5 {

bool StatisticsBase::StatCmp::operator()(const Stat* s1, const Stat* s2) const {
  return s1->getName() < s2->getName();
}

StatisticsBase::iterator::value_type StatisticsBase::iterator::operator*() const {
  return std::make_pair((*d_it)->getName(), (*d_it)->getValue());
}

StatisticsBase::StatisticsBase() :
  d_stats() {
}

StatisticsBase::StatisticsBase(const StatisticsBase& stats) :
  d_stats() {
}

StatisticsBase& StatisticsBase::operator=(const StatisticsBase& stats) {
  return *this;
}

void Statistics::copyFrom(const StatisticsBase& stats) {
  // This is ugly, but otherwise we have to introduce a "friend" relation for
  // Base to its derived class (really obnoxious).
  const StatisticsBase::const_iterator i_begin = stats.begin();
  const StatisticsBase::const_iterator i_end = stats.end();
  for(StatisticsBase::const_iterator i = i_begin; i != i_end; ++i) {
    SExprStat* p = new SExprStat((*i).first, (*i).second);
    d_stats.insert(p);
  }
}

void Statistics::clear() {
  for(StatSet::iterator i = d_stats.begin(); i != d_stats.end(); ++i) {
    delete *i;
  }
  d_stats.clear();
}

Statistics::Statistics(const StatisticsBase& stats) :
  StatisticsBase(stats) {
  copyFrom(stats);
}

Statistics::Statistics(const Statistics& stats) :
  StatisticsBase(stats) {
  copyFrom(stats);
}

Statistics::~Statistics() {
  clear();
}

Statistics& Statistics::operator=(const StatisticsBase& stats) {
  clear();
  this->StatisticsBase::operator=(stats);
  copyFrom(stats);

  return *this;
}

Statistics& Statistics::operator=(const Statistics& stats) {
  return this->operator=((const StatisticsBase&)stats);
}

StatisticsBase::const_iterator StatisticsBase::begin() const {
  return iterator(d_stats.begin());
}

StatisticsBase::const_iterator StatisticsBase::end() const {
  return iterator(d_stats.end());
}

void StatisticsBase::flushInformation(std::ostream &out) const {
#ifdef CVC4_STATISTICS_ON
  for(StatSet::iterator i = d_stats.begin();
      i != d_stats.end();
      ++i) {
    Stat* s = *i;
    out << s->getName() << ", ";
    s->flushInformation(out);
    out << std::endl;
  }
#endif /* CVC4_STATISTICS_ON */
}

void StatisticsBase::safeFlushInformation(int fd) const {
#ifdef CVC4_STATISTICS_ON
  for (StatSet::iterator i = d_stats.begin(); i != d_stats.end(); ++i) {
    Stat* s = *i;
    safe_print(fd, s->getName());
    safe_print(fd, ", ");
    s->safeFlushInformation(fd);
    safe_print(fd, "\n");
  }
#endif /* CVC4_STATISTICS_ON */
}

SExpr StatisticsBase::getStatistic(std::string name) const {
  SExpr value;
  IntStat s(name, 0);
  StatSet::iterator i = d_stats.find(&s);
  if(i != d_stats.end()) {
    return (*i)->getValue();
  } else {
    return SExpr();
  }
}

}  // namespace cvc5
