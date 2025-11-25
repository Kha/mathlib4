/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.PointwiseConvergence
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Topology.Maps.Basic

/-!
# The topology of pointwise convergence is locally convex

We prove that the topology of pointwise convergence is induced by a family of seminorms and
that it is locally convex in the topological sense

* `PointwiseConvergenceCLM.seminorm`: the seminorms on `E →SLₚₜ[σ] F` given by `A ↦ ‖A x‖` for fixed
`x : E`.
* `PointwiseConvergenceCLM.withSeminorm`: the topology is induced by the seminorms.
* `PointwiseConvergenceCLM.instLocallyConvexSpace`: `E →SLₚₜ[σ] F` is locally convex.

-/

@[expose] public section

variable {R 𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]

namespace PointwiseConvergenceCLM

section NormedSpace

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
protected def seminorm (x : E) : Seminorm 𝕜₂ (E →SLₚₜ[σ] F) where
  toFun A := ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [norm_smul]

variable (σ E F) in
/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
protected abbrev seminormFamily : SeminormFamily 𝕜₂ (E →SLₚₜ[σ] F) E :=
  PointwiseConvergenceCLM.seminorm

variable (σ E F) in
/-- The coercion `E →SLₚₜ[σ] F` to `E → F` as a linear map.

The topology on `E →SLₚₜ[σ] F` is induced by this map. -/
def inducingFn : (E →SLₚₜ[σ] F) →ₗ[𝕜₂] (E → F) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (σ E F) in
theorem isInducing_inducingFn : Topology.IsInducing (inducingFn σ E F) :=
  (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).isInducing

lemma withSeminorms : WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F) :=
  let e : E ≃ (Σ _ : E, Fin 1) := .symm <| .sigmaUnique _ _
  (isInducing_inducingFn σ E F).withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ F)
    |>.congr_equiv e

end NormedSpace

section IsTopologicalAddGroup

variable [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜₂ F]
  [Semiring R] [PartialOrder R]
  [Module R F] [ContinuousConstSMul R F] [LocallyConvexSpace R F] [SMulCommClass 𝕜₂ R F]

instance : LocallyConvexSpace R (E →SLₚₜ[σ] F) :=
  UniformConvergenceCLM.locallyConvexSpace R {(s : Set E) | Set.Finite s} ⟨∅, Set.finite_empty⟩
    (directedOn_of_sup_mem fun _ _ => Set.Finite.union)

end IsTopologicalAddGroup

end PointwiseConvergenceCLM
