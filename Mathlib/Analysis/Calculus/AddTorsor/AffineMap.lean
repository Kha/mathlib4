/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.TypeStar
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main definitions:

* `ContinuousAffineMap.contDiff`: a continuous affine map is smooth

-/

@[expose] public section
namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
theorem contDiff {n : WithTop ℕ∞} (f : V →ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

theorem differentiable (f : V →ᴬ[𝕜] W) : Differentiable 𝕜 f :=
  f.contDiff.differentiable le_rfl

theorem differentiableAt (f : V →ᴬ[𝕜] W) {x : V} : DifferentiableAt 𝕜 f x :=
  f.differentiable x

theorem differentiableOn (f : V →ᴬ[𝕜] W) {s : Set V} : DifferentiableOn 𝕜 f s :=
  f.differentiable.differentiableOn

theorem differentiableWithinAt (f : V →ᴬ[𝕜] W) {s : Set V} {x : V} :
    DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

@[simp] theorem fderiv (f : V →ᴬ[𝕜] W) {x : V} : fderiv 𝕜 f x = f.contLinear := by
  conv_lhs => rw [f.decomp]
  rw [fderiv_add f.contLinear.differentiableAt]; swap
  · exact differentiableAt_const _
  simp only [fderiv_const, Pi.zero_apply, add_zero, ContinuousLinearMap.fderiv]

end ContinuousAffineMap
