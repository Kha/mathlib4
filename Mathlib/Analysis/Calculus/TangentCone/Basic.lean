/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Field
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Closure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.IsLUB
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Basic properties of tangent cones and sets with unique differentiability property

In this file we prove basic lemmas about `tangentConeAt`, `UniqueDiffWithinAt`,
and `UniqueDiffOn`.
-/

@[expose] public section

open Filter Set Metric NormedField
open scoped Topology Pointwise

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}

section TVS
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem mem_tangentConeAt_of_pow_smul {r : 𝕜} (hr₀ : r ≠ 0) (hr : ‖r‖ < 1)
    (hs : ∀ᶠ n : ℕ in atTop, x + r ^ n • y ∈ s) : y ∈ tangentConeAt 𝕜 s x := by
  refine ⟨fun n ↦ (r ^ n)⁻¹, fun n ↦ r ^ n • y, hs, ?_, ?_⟩
  · simp only [norm_inv, norm_pow, ← inv_pow]
    exact tendsto_pow_atTop_atTop_of_one_lt <| (one_lt_inv₀ (norm_pos_iff.2 hr₀)).2 hr
  · simp only [inv_smul_smul₀ (pow_ne_zero _ hr₀), tendsto_const_nhds]

@[simp]
theorem tangentConeAt_univ : tangentConeAt 𝕜 univ x = univ :=
  let ⟨_r, hr₀, hr⟩ := exists_norm_lt_one 𝕜
  eq_univ_of_forall fun _ ↦ mem_tangentConeAt_of_pow_smul (norm_pos_iff.1 hr₀) hr <|
    Eventually.of_forall fun _ ↦ mem_univ _

@[deprecated (since := "2025-04-27")] alias tangentCone_univ := tangentConeAt_univ

@[gcongr]
theorem tangentConeAt_mono (h : s ⊆ t) : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  rintro y ⟨c, d, ds, ctop, clim⟩
  exact ⟨c, d, mem_of_superset ds fun n hn => h hn, ctop, clim⟩

@[deprecated (since := "2025-04-27")] alias tangentCone_mono := tangentConeAt_mono

/--
Given `x ∈ s` and a field extension `𝕜 ⊆ 𝕜'`, the tangent cone of `s` at `x` with
respect to `𝕜` is contained in the tangent cone of `s` at `x` with respect to `𝕜'`.
-/
theorem tangentConeAt_mono_field {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [Module 𝕜' E] [IsScalarTower 𝕜 𝕜' E] : tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜' s x := by
  intro α hα
  simp only [tangentConeAt, eventually_atTop, ge_iff_le, tendsto_norm_atTop_iff_cobounded,
    mem_setOf_eq] at hα ⊢
  obtain ⟨c, d, ⟨a, h₁a⟩, h₁, h₂⟩ := hα
  use ((algebraMap 𝕜 𝕜') ∘ c), d
  constructor
  · use a
  · constructor
    · intro β hβ
      rw [mem_map, mem_atTop_sets]
      obtain ⟨n, hn⟩ := mem_atTop_sets.1
        (mem_map.1 (h₁ (tendsto_algebraMap_cobounded (𝕜 := 𝕜) (𝕜' := 𝕜') hβ)))
      use n, fun _ _ ↦ by simp_all
    · simpa

variable [ContinuousSMul 𝕜 E]

/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
theorem tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α → 𝕜} {d : α → E}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • d n) l (𝓝 y)) :
    Tendsto d l (𝓝 0) := by
  have : ∀ᶠ n in l, (c n)⁻¹ • c n • d n = d n :=
    (eventually_ne_of_tendsto_norm_atTop hc 0).mono fun n hn ↦ inv_smul_smul₀ hn (d n)
  rw [tendsto_norm_atTop_iff_cobounded] at hc
  simpa using Tendsto.congr' this <| (tendsto_inv₀_cobounded.comp hc).smul hd

variable [ContinuousAdd E]

theorem tangentConeAt_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
    tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 t x := by
  rintro y ⟨c, d, ds, ctop, clim⟩
  refine ⟨c, d, ?_, ctop, clim⟩
  suffices Tendsto (fun n => x + d n) atTop (𝓝[t] x) from
    tendsto_principal.1 (tendsto_inf.1 this).2
  refine (tendsto_inf.2 ⟨?_, tendsto_principal.2 ds⟩).mono_right h
  simpa only [add_zero] using tendsto_const_nhds.add (tangentConeAt.lim_zero atTop ctop clim)

@[deprecated (since := "2025-04-27")] alias tangentCone_mono_nhds := tangentConeAt_mono_nhds

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
theorem tangentConeAt_congr (h : 𝓝[s] x = 𝓝[t] x) : tangentConeAt 𝕜 s x = tangentConeAt 𝕜 t x :=
  Subset.antisymm (tangentConeAt_mono_nhds h.le) (tangentConeAt_mono_nhds h.ge)

@[deprecated (since := "2025-04-27")] alias tangentCone_congr := tangentConeAt_congr

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
theorem tangentConeAt_inter_nhds (ht : t ∈ 𝓝 x) : tangentConeAt 𝕜 (s ∩ t) x = tangentConeAt 𝕜 s x :=
  tangentConeAt_congr (nhdsWithin_restrict' _ ht).symm

@[deprecated (since := "2025-04-27")] alias tangentCone_inter_nhds := tangentConeAt_inter_nhds

end TVS

section Normed
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {x y : E} {s t : Set E}

@[simp]
theorem tangentConeAt_closure : tangentConeAt 𝕜 (closure s) x = tangentConeAt 𝕜 s x := by
  refine Subset.antisymm ?_ (tangentConeAt_mono subset_closure)
  rintro y ⟨c, d, ds, ctop, clim⟩
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have : ∀ᶠ n in atTop, ∃ d', x + d' ∈ s ∧ dist (c n • d n) (c n • d') < u n := by
    filter_upwards [ctop.eventually_gt_atTop 0, ds] with n hn hns
    rcases Metric.mem_closure_iff.mp hns (u n / ‖c n‖) (div_pos (u_pos n) hn) with ⟨y, hys, hy⟩
    refine ⟨y - x, by simpa, ?_⟩
    rwa [dist_smul₀, ← dist_add_left x, add_sub_cancel, ← lt_div_iff₀' hn]
  simp only [Filter.skolem, eventually_and] at this
  rcases this with ⟨d', hd's, hd'⟩
  exact ⟨c, d', hd's, ctop, clim.congr_dist
    (squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) (hd'.mono fun _ ↦ le_of_lt) u_lim)⟩

/-- The tangent cone at a non-isolated point contains `0`. -/
theorem zero_mem_tangentCone {s : Set E} {x : E} (hx : x ∈ closure s) :
    0 ∈ tangentConeAt 𝕜 s x := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / (d n) ^ (1/2)`, then `c n` tends to infinity, but `c n • d n` tends to `0`. By definition,
  this shows that `0` belongs to the tangent cone. -/
  obtain ⟨u, -, hu, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n ∧ u n < 1) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto' one_pos
  choose u_pos u_lt_one using hu
  choose v hvs hvu using fun n ↦ Metric.mem_closure_iff.mp hx _ (mul_pos (u_pos n) (u_pos n))
  let d n := v n - x
  let ⟨r, hr⟩ := exists_one_lt_norm 𝕜
  have A n := exists_nat_pow_near (one_le_inv_iff₀.mpr ⟨u_pos n, (u_lt_one n).le⟩) hr
  choose m hm_le hlt_m using A
  set c := fun n ↦ r ^ (m n + 1)
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    simp only [c, norm_pow]
    refine tendsto_atTop_mono (fun n ↦ (hlt_m n).le) <| .inv_tendsto_nhdsGT_zero ?_
    exact tendsto_nhdsWithin_iff.mpr ⟨u_lim, .of_forall u_pos⟩
  refine ⟨c, d, .of_forall <| by simpa [d], c_lim, ?_⟩
  have Hle n : ‖c n • d n‖ ≤ ‖r‖ * u n := by
    specialize u_pos n
    calc
      ‖c n • d n‖ ≤ (u n)⁻¹ * ‖r‖ * (u n * u n) := by
        simp only [c, norm_smul, norm_pow, pow_succ, norm_mul, d, ← dist_eq_norm']
        gcongr
        exacts [hm_le n, (hvu n).le]
      _ = ‖r‖ * u n := by field
  refine squeeze_zero_norm Hle ?_
  simpa using tendsto_const_nhds.mul u_lim

/-- If `x` is not an accumulation point of `s`, then the tangent cone of `s` at `x`
is a subset of `{0}`. -/
theorem tangentConeAt_subset_zero (hx : ¬AccPt x (𝓟 s)) : tangentConeAt 𝕜 s x ⊆ 0 := by
  rintro y ⟨c, d, hds, hc, hcd⟩
  suffices ∀ᶠ n in .atTop, d n = 0 from
    tendsto_nhds_unique hcd <| tendsto_const_nhds.congr' <| this.mono fun n hn ↦ by simp [hn]
  simp only [accPt_iff_frequently, not_frequently, not_and', ne_eq, not_not] at hx
  have : Tendsto (x + d ·) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tangentConeAt.lim_zero _ hc hcd)
  filter_upwards [this.eventually hx, hds] with n h₁ h₂
  simpa using h₁ h₂

theorem UniqueDiffWithinAt.accPt [Nontrivial E] (h : UniqueDiffWithinAt 𝕜 s x) : AccPt x (𝓟 s) := by
  by_contra! h'
  have : Dense (Submodule.span 𝕜 (0 : Set E) : Set E) :=
    h.1.mono <| by gcongr; exact tangentConeAt_subset_zero h'
  simp [dense_iff_closure_eq] at this

end Normed

section UniqueDiff

/-!
### Properties of `UniqueDiffWithinAt` and `UniqueDiffOn`

This section is devoted to properties of the predicates `UniqueDiffWithinAt` and `UniqueDiffOn`. -/

section Module
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}

theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn 𝕜 s) (h : x ∈ s) :
    UniqueDiffWithinAt 𝕜 s x :=
  hs x h

@[simp]
theorem uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 univ x := by
  rw [uniqueDiffWithinAt_iff, tangentConeAt_univ]
  simp

@[simp]
theorem uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E) :=
  fun _ _ => uniqueDiffWithinAt_univ

theorem uniqueDiffOn_empty : UniqueDiffOn 𝕜 (∅ : Set E) :=
  fun _ hx => hx.elim

theorem UniqueDiffWithinAt.congr_pt (h : UniqueDiffWithinAt 𝕜 s x) (hy : x = y) :
    UniqueDiffWithinAt 𝕜 s y := hy ▸ h

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [Module 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and that `x ∈ s` is a point
of unique differentiability with respect to the set `s` and the smaller field `𝕜`, then `x` is also
a point of unique differentiability with respect to the set `s` and the larger field `𝕜'`.
-/
theorem UniqueDiffWithinAt.mono_field (h₂s : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜' s x := by
  simp_all only [uniqueDiffWithinAt_iff, and_true]
  apply Dense.mono _ h₂s.1
  trans ↑(Submodule.span 𝕜 (tangentConeAt 𝕜' s x))
  <;> simp [Submodule.span_mono tangentConeAt_mono_field]

/--
Assume that `E` is a normed vector space over normed fields `𝕜 ⊆ 𝕜'` and all points of `s` are
points of unique differentiability with respect to the smaller field `𝕜`, then they are also points
of unique differentiability with respect to the larger field `𝕜`.
-/
theorem UniqueDiffOn.mono_field (h₂s : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜' s := fun x hx ↦ (h₂s x hx).mono_field

end Module

section TVS
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {x y : E} {s t : Set E}
variable [ContinuousAdd E] [ContinuousSMul 𝕜 E]

theorem UniqueDiffWithinAt.mono_nhds (h : UniqueDiffWithinAt 𝕜 s x) (st : 𝓝[s] x ≤ 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 t x := by
  simp only [uniqueDiffWithinAt_iff] at *
  rw [mem_closure_iff_nhdsWithin_neBot] at h ⊢
  exact ⟨h.1.mono <| Submodule.span_mono <| tangentConeAt_mono_nhds st, h.2.mono st⟩

theorem UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ t) :
    UniqueDiffWithinAt 𝕜 t x :=
  h.mono_nhds <| nhdsWithin_mono _ st

theorem uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x) :
    UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x :=
  ⟨fun h => h.mono_nhds <| le_of_eq st, fun h => h.mono_nhds <| le_of_eq st.symm⟩

theorem uniqueDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict' _ ht).symm

theorem UniqueDiffWithinAt.inter (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝 x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter ht).2 hs

theorem uniqueDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x ↔ UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_congr <| (nhdsWithin_restrict'' _ ht).symm

theorem UniqueDiffWithinAt.inter' (hs : UniqueDiffWithinAt 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
    UniqueDiffWithinAt 𝕜 (s ∩ t) x :=
  (uniqueDiffWithinAt_inter' ht).2 hs

theorem uniqueDiffWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) : UniqueDiffWithinAt 𝕜 s x := by
  simpa only [univ_inter] using uniqueDiffWithinAt_univ.inter h

theorem IsOpen.uniqueDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueDiffWithinAt 𝕜 s x :=
  uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds hs xs)

theorem UniqueDiffOn.inter (hs : UniqueDiffOn 𝕜 s) (ht : IsOpen t) : UniqueDiffOn 𝕜 (s ∩ t) :=
  fun x hx => (hs x hx.1).inter (IsOpen.mem_nhds ht hx.2)

theorem IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 𝕜 s :=
  fun _ hx => IsOpen.uniqueDiffWithinAt hs hx

end TVS

section Normed
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {x y : E} {s t : Set E}

@[simp]
theorem uniqueDiffWithinAt_closure :
    UniqueDiffWithinAt 𝕜 (closure s) x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp [uniqueDiffWithinAt_iff]

protected alias ⟨UniqueDiffWithinAt.of_closure, UniqueDiffWithinAt.closure⟩ :=
  uniqueDiffWithinAt_closure

theorem UniqueDiffWithinAt.mono_closure (h : UniqueDiffWithinAt 𝕜 s x) (st : s ⊆ closure t) :
    UniqueDiffWithinAt 𝕜 t x :=
  (h.mono st).of_closure

end Normed

end UniqueDiff
