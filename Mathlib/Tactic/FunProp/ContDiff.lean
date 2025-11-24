/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Tactic.Linter.DeprecatedModule
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Algebra.Order.Module.Algebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

deprecated_module
  "fun_prop knows about ContDiff(At/On) directly; no need to import this file any more"
  (since := "2025-05-13")
