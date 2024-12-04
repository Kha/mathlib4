/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Analytic.Basic

/-!
# Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `Fin n` of cardinality `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this file, we implement this. The new power series is called `p.changeOrigin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open. All these arguments
require the target space to be complete, as otherwise the series might not converge.

### Main results

In a complete space, if a function admits a power series in a ball, then it is analytic at any
point `y` of this ball, and the power series there can be expressed in terms of the initial power
series `p` as `p.changeOrigin y`. See `HasFPowerSeriesOnBall.changeOrigin`. It follows in particular
that the set of points at which a given function is analytic is open, see `isOpen_analyticAt`.
-/

noncomputable section

open scoped NNReal ENNReal Topology
open Filter Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
[NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

section

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r : ℝ≥0}

/-- A term of `FormalMultilinearSeries.changeOriginSeries`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.changeOrigin x` is a formal multilinear series such that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense. Each term of `p.changeOrigin x`
is itself an analytic function of `x` given by the series `p.changeOriginSeries`. Each term in
`changeOriginSeries` is the sum of `changeOriginSeriesTerm`'s over all `s` of cardinality `l`.
The definition is such that `p.changeOriginSeriesTerm k l s hs (fun _ ↦ x) (fun _ ↦ y) =
p (k + l) (s.piecewise (fun _ ↦ x) (fun _ ↦ y))`
-/
def changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    E[×l]→L[𝕜] E[×k]→L[𝕜] F :=
  let a := ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
  a (p (k + l))

/-- Formula for the application of `changeOriginSeriesTerm` on nonconstant vectors. -/
theorem changeOriginSeriesTerm_apply' {k l : ℕ} (s : Finset (Fin (k + l))) (hs : s.card = l)
    (z : Fin (k + l) → E) :
    p.changeOriginSeriesTerm k l s hs (fun (i : Fin l) ↦ z (s.orderEmbOfFin hs i))
      (fun (j : Fin k) ↦ z (sᶜ.orderEmbOfFin
        (by rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right]) j)) =
    p (k + l) z := by
  have h's : sᶜ.card = k := by
    rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right]
  simp only [changeOriginSeriesTerm, ContinuousMultilinearMap.curryFinFinset_apply]
  congr with i
  set m := (finSumEquivOfFinset hs h's).symm i
  have im : i = finSumEquivOfFinset hs h's m := by simp [m]
  clear_value m
  cases m <;> simp [im]

theorem changeOriginSeriesTerm_apply (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l)
    (x y : E) :
    (p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y) =
      p (k + l) (s.piecewise (fun _ => x) fun _ => y) :=
  ContinuousMultilinearMap.curryFinFinset_apply_const _ _ _ _ _

@[simp]
theorem norm_changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖ = ‖p (k + l)‖ := by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.norm_map]

@[simp]
theorem nnnorm_changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    ‖p.changeOriginSeriesTerm k l s hs‖₊ = ‖p (k + l)‖₊ := by
  simp only [changeOriginSeriesTerm, LinearIsometryEquiv.nnnorm_map]

theorem nnnorm_changeOriginSeriesTerm_apply_le (k l : ℕ) (s : Finset (Fin (k + l)))
    (hs : s.card = l) (x y : E) :
    ‖p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y‖₊ ≤
      ‖p (k + l)‖₊ * ‖x‖₊ ^ l * ‖y‖₊ ^ k := by
  rw [← p.nnnorm_changeOriginSeriesTerm k l s hs, ← Fin.prod_const, ← Fin.prod_const]
  apply ContinuousMultilinearMap.le_of_opNNNorm_le
  apply ContinuousMultilinearMap.le_opNNNorm

/-- The power series for `f.changeOrigin k`.

Given a formal multilinear series `p` and a point `x` in its ball of convergence,
`p.changeOrigin x` is a formal multilinear series such that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense. Its `k`-th term is the sum of
the series `p.changeOriginSeries k`. -/
def changeOriginSeries (k : ℕ) : FormalMultilinearSeries 𝕜 E (E[×k]→L[𝕜] F) := fun l =>
  ∑ s : { s : Finset (Fin (k + l)) // Finset.card s = l }, p.changeOriginSeriesTerm k l s s.2

/-- Two strictly monotone functions from `Fin n` are equal provided that their ranges are included
in one another. -/
lemma _root_.Fin.strictMono_unique_of_range_subset {α : Type*} [Preorder α] {n : ℕ}
    {f g : Fin n → α} (hf : StrictMono f) (hg : StrictMono g)
    (h : range f ⊆ range g) : f = g := by
  apply (hf.range_inj hg).1
  apply Finite.eq_of_subset_of_card_le (finite_range g) h
  rw [Nat.card_range_of_injective hf.injective, Nat.card_range_of_injective hg.injective]

lemma changeOriginSeries_zero :
    p.changeOriginSeries 0 =
      ((continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv
        |>.toContinuousLinearMap.compFormalMultilinearSeries p) := by
  ext i v w
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
    continuousMultilinearCurryFin0_symm_apply]
  simp only [FormalMultilinearSeries.changeOriginSeries,
    ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.curryFinFinset_apply]
  let A : Inhabited { s : Finset (Fin (0 + i)) // s.card = i } := ⟨Finset.univ, by simp⟩
  let B : Unique { s : Finset (Fin (0 + i)) // s.card = i } := by
    constructor
    rintro ⟨s, hs⟩
    apply Subtype.eq
    apply Finset.eq_univ_of_card
    simp [hs]
  rw [Finset.sum_unique_nonempty _ _ Finset.univ_nonempty]
  have C : 0 + i = i := by exact Nat.zero_add i
  have : p i v = p (0 + i) (v ∘ (Fin.cast C)) := p.congr C.symm (by simp)
  rw [this, ← changeOriginSeriesTerm_apply' p Finset.univ (by simp)]
  congr
  · ext j
    congr
    have D : Fintype.card (Fin (0 + i)) = i := by simp
    have : Fin.cast C ∘ (Finset.univ.orderEmbOfFin D) = id := by
      apply Fin.strictMono_unique_of_range_subset
      · exact StrictMono.comp (Fin.cast_strictMono _) (OrderEmbedding.strictMono _)
      · exact strictMono_id
      · simp
    change j = (Fin.cast C ∘ (Finset.univ.orderEmbOfFin D)) j
    rw [this, id_eq]
  · exact List.ofFn_inj.mp rfl

theorem nnnorm_changeOriginSeries_le_tsum (k l : ℕ) :
    ‖p.changeOriginSeries k l‖₊ ≤
      ∑' _ : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ :=
  (nnnorm_sum_le _ (fun t => changeOriginSeriesTerm p k l (Subtype.val t) t.prop)).trans_eq <| by
    simp_rw [tsum_fintype, nnnorm_changeOriginSeriesTerm (p := p) (k := k) (l := l)]

theorem nnnorm_changeOriginSeries_apply_le_tsum (k l : ℕ) (x : E) :
    ‖p.changeOriginSeries k l fun _ => x‖₊ ≤
      ∑' _ : { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + l)‖₊ * ‖x‖₊ ^ l := by
  rw [NNReal.tsum_mul_right, ← Fin.prod_const]
  exact (p.changeOriginSeries k l).le_of_opNNNorm_le (p.nnnorm_changeOriginSeries_le_tsum _ _) _

/-- Changing the origin of a formal multilinear series `p`, so that
`p.sum (x+y) = (p.changeOrigin x).sum y` when this makes sense.
-/
def changeOrigin (x : E) : FormalMultilinearSeries 𝕜 E F :=
  fun k => (p.changeOriginSeries k).sum x

/-- An auxiliary equivalence useful in the proofs about
`FormalMultilinearSeries.changeOriginSeries`: the set of triples `(k, l, s)`, where `s` is a
`Finset (Fin (k + l))` of cardinality `l` is equivalent to the set of pairs `(n, s)`, where `s` is a
`Finset (Fin n)`.

The forward map sends `(k, l, s)` to `(k + l, s)` and the inverse map sends `(n, s)` to
`(n - Finset.card s, Finset.card s, s)`. The actual definition is less readable because of problems
with non-definitional equalities. -/
@[simps]
def changeOriginIndexEquiv :
    (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) ≃ Σ n : ℕ, Finset (Fin n) where
  toFun s := ⟨s.1 + s.2.1, s.2.2⟩
  invFun s :=
    ⟨s.1 - s.2.card, s.2.card,
      ⟨s.2.map
        (finCongr <| (tsub_add_cancel_of_le <| card_finset_fin_le s.2).symm).toEmbedding,
        Finset.card_map _⟩⟩
  left_inv := by
    rintro ⟨k, l, ⟨s : Finset (Fin <| k + l), hs : s.card = l⟩⟩
    dsimp only [Subtype.coe_mk]
    -- Lean can't automatically generalize `k' = k + l - s.card`, `l' = s.card`, so we explicitly
    -- formulate the generalized goal
    suffices ∀ k' l', k' = k → l' = l → ∀ (hkl : k + l = k' + l') (hs'),
        (⟨k', l', ⟨s.map (finCongr hkl).toEmbedding, hs'⟩⟩ :
          Σk l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) = ⟨k, l, ⟨s, hs⟩⟩ by
      apply this <;> simp only [hs, add_tsub_cancel_right]
    rintro _ _ rfl rfl hkl hs'
    simp only [Equiv.refl_toEmbedding, finCongr_refl, Finset.map_refl, eq_self_iff_true,
      OrderIso.refl_toEquiv, and_self_iff, heq_iff_eq]
  right_inv := by
    rintro ⟨n, s⟩
    simp [tsub_add_cancel_of_le (card_finset_fin_le s), finCongr_eq_equivCast]

lemma changeOriginSeriesTerm_changeOriginIndexEquiv_symm (n t) :
    let s := changeOriginIndexEquiv.symm ⟨n, t⟩
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ ↦ x) (fun _ ↦ y) =
    p n (t.piecewise (fun _ ↦ x) fun _ ↦ y) := by
  have : ∀ (m) (hm : n = m), p n (t.piecewise (fun _ ↦ x) fun _ ↦ y) =
      p m ((t.map (finCongr hm).toEmbedding).piecewise (fun _ ↦ x) fun _ ↦ y) := by
    rintro m rfl
    simp (config := { unfoldPartialApp := true }) [Finset.piecewise]
  simp_rw [changeOriginSeriesTerm_apply, eq_comm]; apply this

theorem changeOriginSeries_summable_aux₁ {r r' : ℝ≥0} (hr : (r + r' : ℝ≥0∞) < p.radius) :
    Summable fun s : Σk l : ℕ, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (s.1 + s.2.1)‖₊ * r ^ s.2.1 * r' ^ s.1 := by
  rw [← changeOriginIndexEquiv.symm.summable_iff]
  dsimp only [Function.comp_def, changeOriginIndexEquiv_symm_apply_fst,
    changeOriginIndexEquiv_symm_apply_snd_fst]
  have : ∀ n : ℕ,
      HasSum (fun s : Finset (Fin n) => ‖p (n - s.card + s.card)‖₊ * r ^ s.card * r' ^ (n - s.card))
        (‖p n‖₊ * (r + r') ^ n) := by
    intro n
    -- TODO: why `simp only [tsub_add_cancel_of_le (card_finset_fin_le _)]` fails?
    convert_to HasSum (fun s : Finset (Fin n) => ‖p n‖₊ * (r ^ s.card * r' ^ (n - s.card))) _
    · ext1 s
      rw [tsub_add_cancel_of_le (card_finset_fin_le _), mul_assoc]
    rw [← Fin.sum_pow_mul_eq_add_pow]
    exact (hasSum_fintype _).mul_left _
  refine NNReal.summable_sigma.2 ⟨fun n => (this n).summable, ?_⟩
  simp only [(this _).tsum_eq]
  exact p.summable_nnnorm_mul_pow hr

theorem changeOriginSeries_summable_aux₂ (hr : (r : ℝ≥0∞) < p.radius) (k : ℕ) :
    Summable fun s : Σl : ℕ, { s : Finset (Fin (k + l)) // s.card = l } =>
      ‖p (k + s.1)‖₊ * r ^ s.1 := by
  rcases ENNReal.lt_iff_exists_add_pos_lt.1 hr with ⟨r', h0, hr'⟩
  simpa only [mul_inv_cancel_right₀ (pow_pos h0 _).ne'] using
    ((NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr')).1 k).mul_right (r' ^ k)⁻¹

theorem changeOriginSeries_summable_aux₃ {r : ℝ≥0} (hr : ↑r < p.radius) (k : ℕ) :
    Summable fun l : ℕ => ‖p.changeOriginSeries k l‖₊ * r ^ l := by
  refine NNReal.summable_of_le
    (fun n => ?_) (NNReal.summable_sigma.1 <| p.changeOriginSeries_summable_aux₂ hr k).2
  simp only [NNReal.tsum_mul_right]
  exact mul_le_mul' (p.nnnorm_changeOriginSeries_le_tsum _ _) le_rfl

theorem le_changeOriginSeries_radius (k : ℕ) : p.radius ≤ (p.changeOriginSeries k).radius :=
  ENNReal.le_of_forall_nnreal_lt fun _r hr =>
    le_radius_of_summable_nnnorm _ (p.changeOriginSeries_summable_aux₃ hr k)

theorem nnnorm_changeOrigin_le (k : ℕ) (h : (‖x‖₊ : ℝ≥0∞) < p.radius) :
    ‖p.changeOrigin x k‖₊ ≤
      ∑' s : Σl : ℕ, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1 := by
  refine tsum_of_nnnorm_bounded ?_ fun l => p.nnnorm_changeOriginSeries_apply_le_tsum k l x
  have := p.changeOriginSeries_summable_aux₂ h k
  refine HasSum.sigma this.hasSum fun l => ?_
  exact ((NNReal.summable_sigma.1 this).1 l).hasSum

/-- The radius of convergence of `p.changeOrigin x` is at least `p.radius - ‖x‖`. In other words,
`p.changeOrigin x` is well defined on the largest ball contained in the original ball of
convergence. -/
theorem changeOrigin_radius : p.radius - ‖x‖₊ ≤ (p.changeOrigin x).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r _h0 hr => ?_
  rw [lt_tsub_iff_right, add_comm] at hr
  have hr' : (‖x‖₊ : ℝ≥0∞) < p.radius := (le_add_right le_rfl).trans_lt hr
  apply le_radius_of_summable_nnnorm
  have : ∀ k : ℕ,
      ‖p.changeOrigin x k‖₊ * r ^ k ≤
        (∑' s : Σl : ℕ, { s : Finset (Fin (k + l)) // s.card = l }, ‖p (k + s.1)‖₊ * ‖x‖₊ ^ s.1) *
          r ^ k :=
    fun k => mul_le_mul_right' (p.nnnorm_changeOrigin_le k hr') (r ^ k)
  refine NNReal.summable_of_le this ?_
  simpa only [← NNReal.tsum_mul_right] using
    (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr)).2

/-- `derivSeries p` is a power series for `fderiv 𝕜 f` if `p` is a power series for `f`,
see `HasFPowerSeriesOnBall.fderiv`. -/
def derivSeries : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) :=
  (continuousMultilinearCurryFin1 𝕜 E F : (E[×1]→L[𝕜] F) →L[𝕜] E →L[𝕜] F)
    |>.compFormalMultilinearSeries (p.changeOriginSeries 1)

theorem radius_le_radius_derivSeries : p.radius ≤ p.derivSeries.radius := by
  apply (p.le_changeOriginSeries_radius 1).trans (radius_le_of_le (fun n ↦ ?_))
  apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
  apply mul_le_of_le_one_left (norm_nonneg  _)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

end

-- From this point on, assume that the space is complete, to make sure that series that converge
-- in norm also converge in `F`.
variable [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F) {x y : E}

theorem hasFPowerSeriesOnBall_changeOrigin (k : ℕ) (hr : 0 < p.radius) :
    HasFPowerSeriesOnBall (fun x => p.changeOrigin x k) (p.changeOriginSeries k) 0 p.radius :=
  have := p.le_changeOriginSeries_radius k
  ((p.changeOriginSeries k).hasFPowerSeriesOnBall (hr.trans_le this)).mono hr this

/-- Summing the series `p.changeOrigin x` at a point `y` gives back `p (x + y)`. -/
theorem changeOrigin_eval (h : (‖x‖₊ + ‖y‖₊ : ℝ≥0∞) < p.radius) :
    (p.changeOrigin x).sum y = p.sum (x + y) := by
  have radius_pos : 0 < p.radius := lt_of_le_of_lt (zero_le _) h
  have x_mem_ball : x ∈ EMetric.ball (0 : E) p.radius :=
    mem_emetric_ball_zero_iff.2 ((le_add_right le_rfl).trans_lt h)
  have y_mem_ball : y ∈ EMetric.ball (0 : E) (p.changeOrigin x).radius := by
    refine mem_emetric_ball_zero_iff.2 (lt_of_lt_of_le ?_ p.changeOrigin_radius)
    rwa [lt_tsub_iff_right, add_comm]
  have x_add_y_mem_ball : x + y ∈ EMetric.ball (0 : E) p.radius := by
    refine mem_emetric_ball_zero_iff.2 (lt_of_le_of_lt ?_ h)
    exact mod_cast nnnorm_add_le x y
  set f : (Σ k l : ℕ, { s : Finset (Fin (k + l)) // s.card = l }) → F := fun s =>
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have hsf : Summable f := by
    refine .of_nnnorm_bounded _ (p.changeOriginSeries_summable_aux₁ h) ?_
    rintro ⟨k, l, s, hs⟩
    dsimp only [Subtype.coe_mk]
    exact p.nnnorm_changeOriginSeriesTerm_apply_le _ _ _ _ _ _
  have hf : HasSum f ((p.changeOrigin x).sum y) := by
    refine HasSum.sigma_of_hasSum ((p.changeOrigin x).summable y_mem_ball).hasSum (fun k => ?_) hsf
    · dsimp only [f]
      refine ContinuousMultilinearMap.hasSum_eval ?_ _
      have := (p.hasFPowerSeriesOnBall_changeOrigin k radius_pos).hasSum x_mem_ball
      rw [zero_add] at this
      refine HasSum.sigma_of_hasSum this (fun l => ?_) ?_
      · simp only [changeOriginSeries, ContinuousMultilinearMap.sum_apply]
        apply hasSum_fintype
      · refine .of_nnnorm_bounded _
          (p.changeOriginSeries_summable_aux₂ (mem_emetric_ball_zero_iff.1 x_mem_ball) k)
            fun s => ?_
        refine (ContinuousMultilinearMap.le_opNNNorm _ _).trans_eq ?_
        simp
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine HasSum.sigma_of_hasSum
    (p.hasSum x_add_y_mem_ball) (fun n => ?_) (changeOriginIndexEquiv.symm.summable_iff.2 hsf)
  erw [(p n).map_add_univ (fun _ => x) fun _ => y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype (fun c => f (changeOriginIndexEquiv.symm ⟨n, c⟩))

/-- Power series terms are analytic as we vary the origin -/
theorem analyticAt_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) (rp : p.radius > 0) (n : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ p.changeOrigin x n) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin p n rp).analyticAt

end FormalMultilinearSeries


section

variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
  {x y : E} {r : ℝ≥0∞}

/-- If a function admits a power series expansion `p` within a set `s` on a ball `B (x, r)`, then
it also admits a power series on any subball of this ball (even with a different center provided
it belongs to `s`), given by `p.changeOrigin`. -/
theorem HasFPowerSeriesWithinOnBall.changeOrigin (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (h : (‖y‖₊ : ℝ≥0∞) < r) (hy : x + y ∈ insert x s) :
    HasFPowerSeriesWithinOnBall f (p.changeOrigin y) s (x + y) (r - ‖y‖₊) where
  r_le := by
    apply le_trans _ p.changeOrigin_radius
    exact tsub_le_tsub hf.r_le le_rfl
  r_pos := by simp [h]
  hasSum {z} h'z hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right, add_comm] at hz
      rw [p.changeOrigin_eval (hz.trans_le hf.r_le), add_assoc, hf.sum]
      · have : insert (x + y) s ⊆ insert (x + y) (insert x s) := by
          apply insert_subset_insert (subset_insert _ _)
        rw [insert_eq_of_mem hy] at this
        apply this
        simpa [add_assoc] using h'z
      refine mem_emetric_ball_zero_iff.2 (lt_of_le_of_lt ?_ hz)
      exact mod_cast nnnorm_add_le y z
    rw [this]
    apply (p.changeOrigin y).hasSum
    refine EMetric.ball_subset_ball (le_trans ?_ p.changeOrigin_radius) hz
    exact tsub_le_tsub hf.r_le le_rfl

/-- If a function admits a power series expansion `p` on a ball `B (x, r)`, then it also admits a
power series on any subball of this ball (even with a different center), given by `p.changeOrigin`.
-/
theorem HasFPowerSeriesOnBall.changeOrigin (hf : HasFPowerSeriesOnBall f p x r)
    (h : (‖y‖₊ : ℝ≥0∞) < r) : HasFPowerSeriesOnBall f (p.changeOrigin y) (x + y) (r - ‖y‖₊) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.changeOrigin h (by simp)

/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
theorem HasFPowerSeriesWithinOnBall.analyticWithinAt_of_mem
    (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (h : y ∈ insert x s ∩ EMetric.ball x r) : AnalyticWithinAt 𝕜 f s y := by
  have : (‖y - x‖₊ : ℝ≥0∞) < r := by simpa [edist_eq_coe_nnnorm_sub] using h.2
  have := hf.changeOrigin this (by simpa using h.1)
  rw [add_sub_cancel] at this
  exact this.analyticWithinAt

/-- If a function admits a power series expansion `p` on an open ball `B (x, r)`, then
it is analytic at every point of this ball. -/
theorem HasFPowerSeriesOnBall.analyticAt_of_mem (hf : HasFPowerSeriesOnBall f p x r)
    (h : y ∈ EMetric.ball x r) : AnalyticAt 𝕜 f y := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  rw [← analyticWithinAt_univ]
  exact hf.analyticWithinAt_of_mem (by simpa using h)

theorem HasFPowerSeriesWithinOnBall.analyticOn (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    AnalyticOn 𝕜 f (insert x s ∩ EMetric.ball x r) :=
  fun _ hy ↦ ((analyticWithinAt_insert (y := x)).2 (hf.analyticWithinAt_of_mem hy)).mono
    inter_subset_left

theorem HasFPowerSeriesOnBall.analyticOnNhd (hf : HasFPowerSeriesOnBall f p x r) :
    AnalyticOnNhd 𝕜 f (EMetric.ball x r) :=
  fun _y hy => hf.analyticAt_of_mem hy

@[deprecated (since := "2024-09-26")]
alias HasFPowerSeriesOnBall.analyticOn := HasFPowerSeriesOnBall.analyticOnNhd

variable (𝕜 f) in
/-- For any function `f` from a normed vector space to a Banach space, the set of points `x` such
that `f` is analytic at `x` is open. -/
theorem isOpen_analyticAt : IsOpen { x | AnalyticAt 𝕜 f x } := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, r, hr⟩
  exact mem_of_superset (EMetric.ball_mem_nhds _ hr.r_pos) fun y hy => hr.analyticAt_of_mem hy

theorem AnalyticAt.eventually_analyticAt (h : AnalyticAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, AnalyticAt 𝕜 f y :=
  (isOpen_analyticAt 𝕜 f).mem_nhds h

theorem AnalyticAt.exists_mem_nhds_analyticOnNhd (h : AnalyticAt 𝕜 f x) :
    ∃ s ∈ 𝓝 x, AnalyticOnNhd 𝕜 f s :=
  h.eventually_analyticAt.exists_mem

@[deprecated (since := "2024-09-26")]
alias AnalyticAt.exists_mem_nhds_analyticOn := AnalyticAt.exists_mem_nhds_analyticOnNhd

/-- If we're analytic at a point, we're analytic in a nonempty ball -/
theorem AnalyticAt.exists_ball_analyticOnNhd (h : AnalyticAt 𝕜 f x) :
    ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd 𝕜 f (Metric.ball x r) :=
  Metric.isOpen_iff.mp (isOpen_analyticAt _ _) _ h

@[deprecated (since := "2024-09-26")]
alias AnalyticAt.exists_ball_analyticOn := AnalyticAt.exists_ball_analyticOnNhd

end
