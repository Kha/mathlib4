/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Sequences
import Mathlib.Tactic.NormNum.Basic
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
# Tangent cone in a proper space

In this file we prove that the tangent cone of a set in a proper normed space
at an accumulation point of this set is nontrivial.
-/

@[expose] public section

open Filter Set Metric NormedField
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In a proper space, the tangent cone at a non-isolated point is nontrivial. -/
theorem tangentConeAt_nonempty_of_properSpace [ProperSpace E]
    {s : Set E} {x : E} (hx : AccPt x (𝓟 s)) :
    (tangentConeAt 𝕜 s x ∩ {0}ᶜ).Nonempty := by
  /- Take a sequence `d n` tending to `0` such that `x + d n ∈ s`. Taking `c n` of the order
  of `1 / d n`. Then `c n • d n` belongs to a fixed annulus. By compactness, one can extract
  a subsequence converging to a limit `l`. Then `l` is nonzero, and by definition it belongs to
  the tangent cone. -/
  obtain ⟨u, -, u_pos, u_lim⟩ :
      ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 (0 : ℝ)) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have A n : ∃ y ∈ closedBall x (u n) ∩ s, y ≠ x :=
    (accPt_iff_nhds).mp hx _ (closedBall_mem_nhds _ (u_pos n))
  choose v hv hvx using A
  choose hvu hvs using hv
  let d := fun n ↦ v n - x
  have M n : x + d n ∈ s \ {x} := by simp [d, hvs, hvx]
  let ⟨r, hr⟩ := exists_one_lt_norm 𝕜
  have W n := rescale_to_shell hr zero_lt_one (x := d n) (by simpa using (M n).2)
  choose c c_ne c_le le_c hc using W
  have c_lim : Tendsto (fun n ↦ ‖c n‖) atTop atTop := by
    suffices Tendsto (fun n ↦ ‖c n‖⁻¹ ⁻¹ ) atTop atTop by simpa
    apply tendsto_inv_nhdsGT_zero.comp
    simp only [nhdsWithin, tendsto_inf, tendsto_principal, mem_Ioi, eventually_atTop, ge_iff_le]
    have B (n : ℕ) : ‖c n‖⁻¹ ≤ 1⁻¹ * ‖r‖ * u n := by
      apply (hc n).trans
      gcongr
      simpa [d, dist_eq_norm] using hvu n
    refine ⟨?_, 0, fun n hn ↦ by simpa using c_ne n⟩
    apply squeeze_zero (fun n ↦ by positivity) B
    simpa using u_lim.const_mul _
  obtain ⟨l, l_mem, φ, φ_strict, hφ⟩ :
      ∃ l ∈ Metric.closedBall (0 : E) 1 \ Metric.ball (0 : E) (1 / ‖r‖),
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto ((fun n ↦ c n • d n) ∘ φ) atTop (𝓝 l) := by
    apply IsCompact.tendsto_subseq _ (fun n ↦ ?_)
    · exact (isCompact_closedBall 0 1).diff Metric.isOpen_ball
    simp only [mem_diff, Metric.mem_closedBall, dist_zero_right, (c_le n).le,
      Metric.mem_ball, not_lt, true_and, le_c n]
  refine ⟨l, ?_, ?_⟩; swap
  · simp only [mem_compl_iff, mem_singleton_iff]
    contrapose! l_mem
    simp only [one_div, l_mem, mem_diff, Metric.mem_closedBall, dist_self, zero_le_one,
      Metric.mem_ball, inv_pos, norm_pos_iff, ne_eq, not_not, true_and]
    contrapose! hr
    simp [hr]
  refine ⟨c ∘ φ, d ∘ φ, .of_forall fun n ↦ ?_, ?_, hφ⟩
  · simpa [d] using hvs (φ n)
  · exact c_lim.comp φ_strict.tendsto_atTop

@[deprecated (since := "2025-04-27")]
alias tangentCone_nonempty_of_properSpace := tangentConeAt_nonempty_of_properSpace
