/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Closure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.NhdsWithin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Piecewise
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Indexed product of sets with unique differentiability property

In this file we prove that the indexed product
of a family sets with unique differentiability property
has the same property, see `UniqueDiffOn.pi` and  `UniqueDiffOn.univ_pi`.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {s : ∀ i, Set (E i)} {x : ∀ i, E i}

/-- The tangent cone of a product contains the tangent cone of each factor. -/
theorem mapsTo_tangentConeAt_pi [DecidableEq ι] {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
    MapsTo (LinearMap.single 𝕜 E i) (tangentConeAt 𝕜 (s i) (x i))
      (tangentConeAt 𝕜 (Set.pi univ s) x) := by
  rintro w ⟨c, d, hd, hc, hy⟩
  have : ∀ n, ∀ j ≠ i, ∃ d', x j + d' ∈ s j ∧ ‖c n • d'‖ < (1 / 2 : ℝ) ^ n := fun n j hj ↦ by
    rcases mem_closure_iff_nhds.1 (hi j hj) _
        (eventually_nhds_norm_smul_sub_lt (c n) (x j) (pow_pos one_half_pos n)) with
      ⟨z, hz, hzs⟩
    exact ⟨z - x j, by simpa using hzs, by simpa using hz⟩
  choose! d' hd's hcd' using this
  refine ⟨c, fun n => Function.update (d' n) i (d n), hd.mono fun n hn j _ => ?_, hc,
      tendsto_pi_nhds.2 fun j => ?_⟩
  · rcases em (j = i) with (rfl | hj) <;> simp [*]
  · rcases em (j = i) with (rfl | hj)
    · simp [hy]
    · suffices Tendsto (fun n => c n • d' n j) atTop (𝓝 0) by simpa [hj]
      refine squeeze_zero_norm (fun n => (hcd' n j hj).le) ?_
      exact tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le one_half_lt_one

@[deprecated (since := "2025-04-27")] alias mapsTo_tangentCone_pi := mapsTo_tangentConeAt_pi

variable (ι E)
variable [Finite ι]

theorem UniqueDiffWithinAt.univ_pi (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (h : ∀ i, UniqueDiffWithinAt 𝕜 (s i) (x i)) : UniqueDiffWithinAt 𝕜 (Set.pi univ s) x := by
  classical
  simp only [uniqueDiffWithinAt_iff, closure_pi_set] at h ⊢
  refine ⟨(dense_pi univ fun i _ => (h i).1).mono ?_, fun i _ => (h i).2⟩
  norm_cast
  simp only [← Submodule.iSup_map_single, iSup_le_iff, LinearMap.map_span, Submodule.span_le,
    ← mapsTo_iff_image_subset]
  exact fun i => (mapsTo_tangentConeAt_pi fun j _ => (h j).2).mono Subset.rfl Submodule.subset_span

theorem UniqueDiffWithinAt.pi (s : ∀ i, Set (E i)) (x : ∀ i, E i)
    (I : Set ι) (h : ∀ i ∈ I, UniqueDiffWithinAt 𝕜 (s i) (x i)) :
    UniqueDiffWithinAt 𝕜 (Set.pi I s) x := by
  classical
  rw [← Set.univ_pi_piecewise_univ]
  refine UniqueDiffWithinAt.univ_pi ι E _ _ fun i => ?_
  by_cases hi : i ∈ I <;> simp [*, uniqueDiffWithinAt_univ]

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.pi (s : ∀ i, Set (E i)) (I : Set ι)
    (h : ∀ i ∈ I, UniqueDiffOn 𝕜 (s i)) : UniqueDiffOn 𝕜 (Set.pi I s) :=
  fun x hx => UniqueDiffWithinAt.pi _ _ _ _ _ fun i hi => h i hi (x i) (hx i hi)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
theorem UniqueDiffOn.univ_pi (s : ∀ i, Set (E i)) (h : ∀ i, UniqueDiffOn 𝕜 (s i)) :
    UniqueDiffOn 𝕜 (Set.pi univ s) :=
  UniqueDiffOn.pi _ _ _ _ fun i _ => h i
