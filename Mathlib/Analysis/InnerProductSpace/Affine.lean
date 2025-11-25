/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.TypeStar
import Mathlib.Analysis.InnerProductSpace.Basic
/-!
# Normed affine spaces over an inner product space
-/

@[expose] public section

variable {𝕜 V P : Type*}

section RCLike
variable [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped InnerProductSpace

theorem inner_vsub_left_eq_zero_symm {a b : P} {v : V} :
    ⟪a -ᵥ b, v⟫_𝕜 = 0 ↔ ⟪b -ᵥ a, v⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev, inner_neg_left, neg_eq_zero]

theorem inner_vsub_right_eq_zero_symm {v : V} {a b : P} :
    ⟪v, a -ᵥ b⟫_𝕜 = 0 ↔ ⟪v, b -ᵥ a⟫_𝕜 = 0 := by
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right, neg_eq_zero]

end RCLike

section Real
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped RealInnerProductSpace

/-!
In this section, the first `left`/`right` indicates where the common argument to `vsub` is,
and the section refers to the argument of `inner` that ends up in the `dist`.

The lemma shapes are such that the relevant argument of `inner` remains unchanged,
and that the other `vsub` preserves the position of the unchanging argument. -/

theorem inner_vsub_vsub_left_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a b ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [dist_eq_norm_vsub V, inner_eq_norm_sq_left_iff, vsub_sub_vsub_cancel_left,
    inner_vsub_right_eq_zero_symm]

theorem inner_vsub_vsub_left_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ b, a -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪c -ᵥ b, a -ᵥ c⟫ = 0 := by
  rw [real_inner_comm, inner_vsub_vsub_left_eq_dist_sq_left_iff, real_inner_comm]

theorem inner_vsub_vsub_right_eq_dist_sq_left_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist a c ^ 2 ↔ ⟪a -ᵥ c, b -ᵥ a⟫ = 0 := by
  rw [dist_eq_norm_vsub V, inner_eq_norm_sq_left_iff, vsub_sub_vsub_cancel_right,
    inner_vsub_right_eq_zero_symm]

theorem inner_vsub_vsub_right_eq_dist_sq_right_iff {a b c : P} :
    ⟪a -ᵥ c, b -ᵥ c⟫ = dist b c ^ 2 ↔ ⟪a -ᵥ b, b -ᵥ c⟫ = 0 := by
  rw [real_inner_comm, inner_vsub_vsub_right_eq_dist_sq_left_iff, real_inner_comm]

end Real
