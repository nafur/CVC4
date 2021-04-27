/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This file provides default weights for the resources spent in the resource
 * manager.
 */

#include "cvc5_public.h"

#ifndef CVC5__RESOURCE_MANAGER_WEIGHTS_H
#define CVC5__RESOURCE_MANAGER_WEIGHTS_H

#include "options/options.h"
#include "options/smt_options.h"

namespace cvc5 {
namespace resources {

bool parseOption(const std::string& optarg, std::string& name, uint64_t& weight)
{
  auto pos = optarg.find('=');
  // Check if there is a '='
  if (pos == std::string::npos) return false;
  // The name is the part before '='
  name = optarg.substr(0, pos);
  // The weight is the part after '='
  std::string num = optarg.substr(pos + 1);
  std::size_t converted;
  weight = std::stoull(num, &converted);
  // Check everything after '=' was converted
  return converted == num.size();
}

template <typename T, typename Weights>
void setWeight(T identifier, uint64_t weight, Weights& weights)
{
  weights[static_cast<size_t>(identifier)] = weight;
}

template <typename Res, typename Cont, typename... Tail>
void loadWeightsFromOption(const std::string& name,
                           uint64_t weight,
                           Res res,
                           Cont& weights,
                           Tail&&... tail)
{
  using theory::toString;
  for (size_t i = 0; i < weights.size(); ++i)
  {
    if (name == toString(static_cast<Res>(i)))
    {
      setWeight(static_cast<Res>(i), weight, weights);
      return;
    }
  }

  if constexpr (sizeof...(Tail) > 0)
  {
    loadWeightsFromOption(name, weight, std::forward<Tail>(tail)...);
  }
  else
  {
    throw OptionException("Did not recognize resource type " + name);
  }
}

template <typename Res, typename CRes, typename Cont, typename... Tail>
void def(Res res, uint64_t weight, CRes cres, Cont& weights, Tail&&... tail)
{
  if constexpr (std::is_same_v<Res, CRes>)
  {
    setWeight(res, weight, weights);
  }
  else if constexpr (sizeof...(Tail) > 0)
  {
    def(res, weight, std::forward<Tail>(tail)...);
  }
  else
  {
    throw OptionException("Could not set default for unknown resource type");
  }
}

template <typename... T>
void loadDefaultWeights(T&&... weights)
{
  using theory::InferenceId;

  def(InferenceId::QUANTIFIERS_INST_E_MATCHING_SIMPLE, 2, weights...);
  def(InferenceId::QUANTIFIERS_INST_E_MATCHING, 2, weights...);
  def(InferenceId::ARRAYS_READ_OVER_WRITE, 4, weights...);
  def(Resource::CnfStep, 4, weights...);
  def(Resource::LemmaStep, 4, weights...);
  def(InferenceId::ARITH_CONF_SIMPLEX, 6, weights...);
  def(Resource::TheoryCheckStep, 7, weights...);
  def(Resource::BvSatPropagateStep, 17, weights...);
  def(Resource::ArithPivotStep, 22, weights...);
}
}  // namespace resources

template <typename... T>
void loadWeights(const Options& opts, T&&... weights)
{
  resources::loadDefaultWeights(std::forward<T>(weights)...);
  for (const auto& opt : opts[options::resourceWeightHolder__option_t()])
  {
    std::string name;
    uint64_t weight;
    if (resources::parseOption(opt, name, weight))
    {
      resources::loadWeightsFromOption(
          name, weight, std::forward<T>(weights)...);
    }
  }
}

}  // namespace cvc5

#endif