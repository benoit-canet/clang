//===--- NegativeArrayIndexAssignmentChecker.h ----------------------*- C++
//-*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This defines NegativeArrayIndexAssignmentChecker, a builtin check in
// ExprEngine
// that performs checks for undefined array subscripts.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ParentMap.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

namespace {
class NegativeArrayIndexAssignmentChecker
    : public Checker<check::PreStmt<ArraySubscriptExpr>> {
  mutable std::unique_ptr<BuiltinBug> BT;
  bool IsIntegerLiteral(const Expr *E) const;
  bool IsLeft(const ArraySubscriptExpr *A, CheckerContext &C) const;
  bool IsRight(const ArraySubscriptExpr *A, CheckerContext &C) const;
  bool CheckCond(BinaryOperator::Opcode op, const Expr *E, int64_t value,
                 CheckerContext &C) const;

public:
  void checkPreStmt(const ArraySubscriptExpr *A, CheckerContext &C) const;
};
} // end anonymous namespace

bool
NegativeArrayIndexAssignmentChecker::IsIntegerLiteral(const Expr *E) const {

  if (E->getStmtClass() != Stmt::UnaryOperatorClass)
    return false;

  const UnaryOperator *U = dyn_cast<UnaryOperator>(E);

  const Expr *S = U->getSubExpr();

  if (S->getStmtClass() != Stmt::IntegerLiteralClass)
    return false;

  return true;
}

bool NegativeArrayIndexAssignmentChecker::IsLeft(const ArraySubscriptExpr *A,
                                                 CheckerContext &C) const {
  const ParentMap &PM = C.getLocationContext()->getParentMap();

  const Stmt *Parent = PM.getParentIgnoreParens(A);
  if (!Parent)
    return false;

  if (Parent->getStmtClass() != Stmt::BinaryOperatorClass)
    return false;

  const BinaryOperator *B = dyn_cast<BinaryOperator>(Parent);

  if (B->getOpcode() != BO_Assign && B->getOpcode() != BO_MulAssign &&
      B->getOpcode() != BO_DivAssign && B->getOpcode() != BO_RemAssign &&
      B->getOpcode() != BO_AddAssign && B->getOpcode() != BO_SubAssign &&
      B->getOpcode() != BO_ShlAssign && B->getOpcode() != BO_ShrAssign &&
      B->getOpcode() != BO_AndAssign && B->getOpcode() != BO_XorAssign &&
      B->getOpcode() != BO_OrAssign)
    return false;

  // check we are on the left of the =
  if (B->getLHS()->getStmtClass() != Stmt::ArraySubscriptExprClass ||
      dyn_cast<ArraySubscriptExpr>(B->getLHS()) != A)
    return false;

  return true;
}

bool NegativeArrayIndexAssignmentChecker::IsRight(const ArraySubscriptExpr *A,
                                                  CheckerContext &C) const {
  const ParentMap &PM = C.getLocationContext()->getParentMap();

  const Stmt *Parent = PM.getParentIgnoreParens(A);
  if (!Parent)
    return false;

  if (Parent->getStmtClass() != Stmt::ImplicitCastExprClass)
    return false;

  const clang::ImplicitCastExpr *Cast =
      dyn_cast<clang::ImplicitCastExpr>(Parent);

  const Stmt *GrandParent = PM.getParentIgnoreParens(Cast);
  if (!GrandParent)
    return false;

  if (GrandParent->getStmtClass() != Stmt::BinaryOperatorClass)
    return false;

  const BinaryOperator *B = dyn_cast<BinaryOperator>(GrandParent);

  if (B->getOpcode() != BO_Assign && B->getOpcode() != BO_MulAssign &&
      B->getOpcode() != BO_DivAssign && B->getOpcode() != BO_RemAssign &&
      B->getOpcode() != BO_AddAssign && B->getOpcode() != BO_SubAssign &&
      B->getOpcode() != BO_ShlAssign && B->getOpcode() != BO_ShrAssign &&
      B->getOpcode() != BO_AndAssign && B->getOpcode() != BO_XorAssign &&
      B->getOpcode() != BO_OrAssign)
    return false;

  // check we are on the left of the =
  if (B->getRHS()->getStmtClass() != Stmt::ImplicitCastExprClass ||
      dyn_cast<clang::ImplicitCastExpr>(B->getRHS()) != Cast)
    return false;

  return true;
}

bool
NegativeArrayIndexAssignmentChecker::CheckCond(clang::BinaryOperatorKind op,
                                               const Expr *E, int64_t value,
                                               CheckerContext &C) const {
  ProgramStateRef state = C.getState();
  SValBuilder &svalBuilder = C.getSValBuilder();
  ConstraintManager &CM = C.getConstraintManager();

  Optional<DefinedSVal> DV =
      state->getSVal(E, C.getLocationContext()).getAs<DefinedSVal>();
  if (!DV)
    return false;
  // First, ensure that the value is >= 0.

  DefinedSVal ReferenceVal = svalBuilder.makeIntVal(value, false);
  SVal Val = svalBuilder.evalBinOp(state, op, *DV, ReferenceVal,
                                   svalBuilder.getConditionType());

  Optional<DefinedSVal> DSVal = Val.getAs<DefinedSVal>();

  if (!DSVal) {
    // The SValBuilder cannot construct a valid SVal for this Condition.
    // This means we cannot properly reason about it.
    return false;
  }

  ProgramStateRef stateTrue, stateFalse;
  std::tie(stateTrue, stateFalse) = CM.assumeDual(state, *DSVal);

  // Is it possible for the value to be less than zero?
  if (stateFalse)
    return false;

  if (!stateTrue)
    return false;

  return true;
}

void
NegativeArrayIndexAssignmentChecker::checkPreStmt(const ArraySubscriptExpr *A,
                                                  CheckerContext &C) const {

  bool isLeft = IsLeft(A, C);
  bool isRight = IsRight(A, C);

  if (!isLeft && !isRight)
    return;

  const Expr *Index = A->getRHS();

  if (IsIntegerLiteral(Index))
    return;

  if (!CheckCond(BO_LT, Index, 0, C))
    return;

  if (!CheckCond(BO_GT, Index, -(1024 * 1024), C))
    return;

  if (!BT) {
    if (isLeft)
      BT.reset(new BuiltinBug(this, "buf[x] = foo with x < 0"));
    else if (isRight)
      BT.reset(new BuiltinBug(this, "foo = buf[x] with x < 0"));
  }

  ExplodedNode *N = C.generateSink();
  if (!N)
    return;

  BugReport *report = new BugReport(*BT, BT->getDescription(), N);
  report->addRange(Index->getSourceRange());
  C.emitReport(report);
}

void ento::registerNegativeArrayIndexAssignmentChecker(CheckerManager &mgr) {
  mgr.registerChecker<NegativeArrayIndexAssignmentChecker>();
}
