/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Util.CompileInductive
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module
  "fun_prop knows about ContDiff(At/On) directly; no need to import this file any more"
  (since := "2025-05-13")
