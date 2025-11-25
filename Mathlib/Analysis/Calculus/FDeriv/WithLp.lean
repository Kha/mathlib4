/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Tactic.TypeStar
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives on `WithLp`
-/

@[expose] public section

open ContinuousLinearMap PiLp WithLp

section PiLp

variable {𝕜 ι : Type*} {E : ι → Type*} {H : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup H] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [NormedSpace 𝕜 H] [Fintype ι] (p) [Fact (1 ≤ p)]
  {f : H → PiLp p E} {f' : H →L[𝕜] PiLp p E} {t : Set H} {y : H}

theorem differentiableWithinAt_piLp :
    DifferentiableWithinAt 𝕜 f t y ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => f x i) t y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiableWithinAt_iff,
    differentiableWithinAt_pi]
  rfl

theorem differentiableAt_piLp :
    DifferentiableAt 𝕜 f y ↔ ∀ i, DifferentiableAt 𝕜 (fun x => f x i) y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiableAt_iff, differentiableAt_pi]
  rfl

theorem differentiableOn_piLp :
    DifferentiableOn 𝕜 f t ↔ ∀ i, DifferentiableOn 𝕜 (fun x => f x i) t := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiableOn_iff, differentiableOn_pi]
  rfl

theorem differentiable_piLp : Differentiable 𝕜 f ↔ ∀ i, Differentiable 𝕜 fun x => f x i := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_differentiable_iff, differentiable_pi]
  rfl

theorem hasStrictFDerivAt_piLp :
    HasStrictFDerivAt f f' y ↔
      ∀ i, HasStrictFDerivAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_hasStrictFDerivAt_iff, hasStrictFDerivAt_pi']
  rfl

theorem hasFDerivWithinAt_piLp :
    HasFDerivWithinAt f f' t y ↔
      ∀ i, HasFDerivWithinAt (fun x => f x i) (PiLp.proj _ _ i ∘L f') t y := by
  rw [← (PiLp.continuousLinearEquiv p 𝕜 E).comp_hasFDerivWithinAt_iff, hasFDerivWithinAt_pi']
  rfl

namespace PiLp

theorem hasStrictFDerivAt_ofLp (f : PiLp p E) :
    HasStrictFDerivAt ofLp (continuousLinearEquiv p 𝕜 _).toContinuousLinearMap f :=
  .of_isLittleO <| (Asymptotics.isLittleO_zero _ _).congr_left fun _ => (sub_self _).symm

@[deprecated hasStrictFDerivAt_ofLp (since := "2025-05-07")]
theorem hasStrictFDerivAt_equiv (f : PiLp p E) :
    HasStrictFDerivAt (WithLp.equiv p _)
      (continuousLinearEquiv p 𝕜 _).toContinuousLinearMap f :=
  hasStrictFDerivAt_ofLp _ f

theorem hasStrictFDerivAt_toLp (f : ∀ i, E i) :
    HasStrictFDerivAt (toLp p) (continuousLinearEquiv p 𝕜 _).symm.toContinuousLinearMap f :=
  .of_isLittleO <| (Asymptotics.isLittleO_zero _ _).congr_left fun _ => (sub_self _).symm

@[deprecated hasStrictFDerivAt_toLp (since := "2025-05-07")]
theorem hasStrictFDerivAt_equiv_symm (f : ∀ i, E i) :
    HasStrictFDerivAt (WithLp.equiv p _).symm
      (continuousLinearEquiv p 𝕜 _).symm.toContinuousLinearMap f :=
  hasStrictFDerivAt_toLp _ f

nonrec theorem hasStrictFDerivAt_apply (f : PiLp p E) (i : ι) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : PiLp p E => f i) (proj p E i) f :=
  (hasStrictFDerivAt_apply i f).comp f (hasStrictFDerivAt_ofLp (𝕜 := 𝕜) p f)

theorem hasFDerivAt_ofLp (f : PiLp p E) :
    HasFDerivAt ofLp (continuousLinearEquiv p 𝕜 _).toContinuousLinearMap f :=
  (hasStrictFDerivAt_ofLp p f).hasFDerivAt

@[deprecated hasFDerivAt_ofLp (since := "2025-05-07")]
theorem hasFDerivAt_equiv (f : PiLp p E) :
    HasFDerivAt (WithLp.equiv _ _) (continuousLinearEquiv p 𝕜 _).toContinuousLinearMap f :=
  hasFDerivAt_ofLp _ f

theorem hasFDerivAt_toLp (f : ∀ i, E i) :
    HasFDerivAt (toLp p) (continuousLinearEquiv p 𝕜 _).symm.toContinuousLinearMap f :=
  (hasStrictFDerivAt_toLp p f).hasFDerivAt

@[deprecated hasFDerivAt_toLp (since := "2025-05-07")]
theorem hasFDerivAt_equiv_symm (f : ∀ i, E i) :
    HasFDerivAt (WithLp.equiv _ _).symm
      (continuousLinearEquiv p 𝕜 _).symm.toContinuousLinearMap f :=
  hasFDerivAt_toLp _ f

nonrec theorem hasFDerivAt_apply (f : PiLp p E) (i : ι) :
    HasFDerivAt (𝕜 := 𝕜) (fun f : PiLp p E => f i) (proj p E i) f :=
  (hasStrictFDerivAt_apply p f i).hasFDerivAt

end PiLp

end PiLp
