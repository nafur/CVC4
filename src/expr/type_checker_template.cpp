/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Dejan Jovanovic, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * TypeChecker implementation.
 */

#include <sstream>

#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/type_checker.h"
#include "expr/type_checker_util.h"

${typechecker_includes}

namespace cvc5 {
namespace expr {

TypeNode TypeChecker::computeType(NodeManager* nodeManager, TNode n, bool check)
{
  TypeNode typeNode;

  // Infer the type
  switch(n.getKind()) {
  case kind::VARIABLE:
  case kind::SKOLEM:
    typeNode = nodeManager->getAttribute(n, TypeAttr());
    break;
  case kind::BUILTIN:
    typeNode = nodeManager->builtinOperatorType();
    break;

${typerules}

  default:
    Debug("getType") << "FAILURE" << std::endl;
    Unhandled() << " " << n.getKind();
  }

  nodeManager->setAttribute(n, TypeAttr(), typeNode);
  nodeManager->setAttribute(n, TypeCheckedAttr(),
                            check || nodeManager->getAttribute(n, TypeCheckedAttr()));

  return typeNode;

}/* TypeChecker::computeType */

bool TypeChecker::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getMetaKind() == kind::metakind::OPERATOR
         || n.getMetaKind() == kind::metakind::PARAMETERIZED
         || n.getMetaKind() == kind::metakind::NULLARY_OPERATOR);

  switch(n.getKind()) {
${construles}

    default:;
  }

  return false;

}/* TypeChecker::computeIsConst */

}  // namespace expr
}  // namespace cvc5
