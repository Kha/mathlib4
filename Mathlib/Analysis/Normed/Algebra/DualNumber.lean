/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Topology.Instances.TrivSqZeroExt
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.TypeStar
import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

/-!
# Results on `DualNumber R` related to the norm

These are just restatements of similar statements about `TrivSqZeroExt R M`.

## Main results

* `exp_eps`

-/

@[expose] public section

open NormedSpace -- For `NormedSpace.exp`.

namespace DualNumber

open TrivSqZeroExt

variable (𝕜 : Type*) {R : Type*}
variable [Field 𝕜] [CharZero 𝕜] [CommRing R] [Algebra 𝕜 R]
variable [UniformSpace R] [IsTopologicalRing R] [T2Space R]

@[simp]
theorem exp_eps : exp 𝕜 (eps : DualNumber R) = 1 + eps :=
  exp_inr _ _

@[simp]
theorem exp_smul_eps (r : R) : exp 𝕜 (r • eps : DualNumber R) = 1 + r • eps := by
  rw [eps, ← inr_smul, exp_inr]

end DualNumber
