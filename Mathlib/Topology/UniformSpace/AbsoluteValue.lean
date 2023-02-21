/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.absolute_value
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Topology.UniformSpace.Basic

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/


open Set Function Filter UniformSpace

open Filter

namespace IsAbsoluteValue

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

variable {R : Type _} [CommRing R] (abv : R → 𝕜) [IsAbsoluteValue abv]

/-- The uniformity coming from an absolute value. -/
def uniformSpaceCore : UniformSpace.Core R :=
  .ofFun (fun x y => abv (y - x)) (by simp [abv_zero]) (fun x y => abv_sub abv y x) fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun x y z h₁ h₂ =>
      calc abv (z - x) = abv ((z - y) + (y - x)) := by rw [sub_add_sub_cancel]
      _ ≤ abv (z - y) + abv (y - x) := abv_add abv _ _
      _ < ε / 2 + ε / 2 := add_lt_add h₂ h₁
      _ = ε := add_halves ε⟩
#align is_absolute_value.uniform_space_core IsAbsoluteValue.uniformSpaceCore

/-- The uniform structure coming from an absolute value. -/
def uniformSpace : UniformSpace R :=
  UniformSpace.ofCore (uniformSpaceCore abv)
#align is_absolute_value.uniform_space IsAbsoluteValue.uniformSpace

theorem mem_uniformity {s : Set (R × R)} :
    s ∈ (uniformSpaceCore abv).uniformity ↔ ∃ ε > 0, ∀ {a b : R}, abv (b - a) < ε → (a, b) ∈ s :=
  ((UniformSpace.Core.hasBasis_ofFun (exists_gt _) _ _ _ _).1 s).trans <| by
    simp only [subset_def, Prod.forall]; rfl
#align is_absolute_value.mem_uniformity IsAbsoluteValue.mem_uniformity

end IsAbsoluteValue
