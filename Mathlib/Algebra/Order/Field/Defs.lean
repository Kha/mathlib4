/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Tactic.Linter.DeprecatedModule
public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Util.CompileInductive
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Data.Nat.Cast.Defs

deprecated_module
"for `[LinearOrderedSemifield]`, use `[Semifield K] [LinearOrder K] [IsStrictOrderedRing K]` \
instead.
for `[LinearOrderedField]`, use `[Field K] [LinearOrder K] [IsStrictOrderedRing K]` instead."
(since := "2025-10-30")
