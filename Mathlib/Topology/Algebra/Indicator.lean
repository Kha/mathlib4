/-
Copyright (c) 2024 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Topology.ContinuousOn

open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {s : Set α} [One β]

@[to_additive]
lemma continuous_mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : ContinuousOn f (closure s)) :
    Continuous (mulIndicator s f) := by
  classical exact continuous_piecewise hs hf continuousOn_const

@[to_additive]
protected lemma Continuous.mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : Continuous f) :
    Continuous (mulIndicator s f) := by
  classical exact hf.piecewise hs continuous_const
