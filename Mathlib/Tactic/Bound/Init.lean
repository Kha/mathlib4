/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Init
public import Aesop.Frontend.Command
public import Batteries.Control.Lemmas
public import Lean.Elab.ErrorExplanation
public import Lean.Meta.Tactic.TryThis
public import Std.Do.Triple.SpecLemmas
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Bound Rule Set

This module defines the `Bound` Aesop rule set which is used by the
`bound` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

public meta section

declare_aesop_rule_sets [Bound]
