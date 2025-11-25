/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Ring.Associated
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Data.Nat.Cast.NeZero
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Ideals in cyclotomic fields

In this file, we prove results about ideals in cyclotomic extensions of `ℚ`.

## Main results

* `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow`: there is only one prime ideal above
  the prime `p` in `ℚ(ζ_pᵏ)`

* `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow`: the residual degree of the prime ideal
  above `p` in `ℚ(ζ_pᵏ)` is `1`.

* `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow`: the ramification index of the prime
  ideal above `p` in `ℚ(ζ_pᵏ)` is `p ^ (k - 1) * (p - 1)`.
-/

@[expose] public section

namespace IsCyclotomicExtension.Rat

open Ideal NumberField

section PrimePow

variable (p k : ℕ) [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

instance isPrime_span_zeta_sub_one : IsPrime (span {hζ.toInteger - 1}) := by
  rw [Ideal.span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime

theorem associated_norm_zeta_sub_one : Associated (Algebra.norm ℤ (hζ.toInteger - 1)) (p : ℤ) := by
  by_cases h : p = 2
  · cases k with
    | zero =>
      rw [h, zero_add, pow_one] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two, h, Int.ofNat_two, Associated.neg_left_iff]
    | succ n =>
      rw [h, add_assoc, one_add_one_eq_two] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two_pow, h, Int.ofNat_two]
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two h]

theorem absNorm_span_zeta_sub_one : absNorm (span {hζ.toInteger - 1}) = p := by
  simpa using congr_arg absNorm <|
    span_singleton_eq_span_singleton.mpr <| associated_norm_zeta_sub_one p k hζ

theorem p_mem_span_zeta_sub_one : (p : 𝓞 K) ∈ span {hζ.toInteger - 1} := by
  convert Ideal.absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm

theorem span_zeta_sub_one_ne_bot : span {hζ.toInteger - 1} ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩

theorem liesOver_span_zeta_sub_one : (span {hζ.toInteger - 1}).LiesOver 𝒑 := by
  rw [liesOver_iff]
  refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ

theorem inertiaDeg_span_zeta_sub_one : inertiaDeg 𝒑 (span {hζ.toInteger - 1}) = 1 := by
  have := liesOver_span_zeta_sub_one p k hζ
  rw [← Nat.pow_right_inj hp.out.one_lt, pow_one, ← absNorm_eq_pow_inertiaDeg' _ hp.out,
    absNorm_span_zeta_sub_one]

attribute [local instance] FractionRing.liftAlgebra in
theorem map_eq_span_zeta_sub_one_pow :
    (map (algebraMap ℤ (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank ℚ K := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have : IsGalois (FractionRing ℤ) (FractionRing (𝓞 K)) := by
    refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv ℤ ℚ).toRingEquiv.symm)
      (g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm) <|
        RingHom.ext fun x ↦ IsFractionRing.algEquiv_commutes (FractionRing.algEquiv ℤ ℚ).symm
          (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [map_span, Set.image_singleton, span_singleton_eq_span_singleton.mpr
    ((associated_norm_zeta_sub_one p k hζ).symm.map (algebraMap ℤ (𝓞 K))),
    ← Algebra.intNorm_eq_norm, Algebra.algebraMap_intNorm_of_isGalois, ← prod_span_singleton]
  conv_lhs =>
    enter [2, σ]
    rw [span_singleton_eq_span_singleton.mpr
      (hζ.toInteger_isPrimitiveRoot.associated_sub_one_map_sub_one σ).symm]
  rw [Finset.prod_const, Finset.card_univ, ← Fintype.card_congr (galRestrict ℤ ℚ K (𝓞 K)).toEquiv,
    ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

theorem ramificationIdx_span_zeta_sub_one :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 (span {hζ.toInteger - 1}) = p ^ k * (p - 1) := by
  have := liesOver_span_zeta_sub_one p k hζ
  have h := isPrime_span_zeta_sub_one p k hζ
  rw [← Nat.totient_prime_pow_succ hp.out, ← finrank _ K,
    IsDedekindDomain.ramificationIdx_eq_multiplicity _ h, map_eq_span_zeta_sub_one_pow p k hζ,
    multiplicity_pow_self (span_zeta_sub_one_ne_bot p k hζ) (isUnit_iff.not.mpr h.ne_top)]
  exact map_ne_bot_of_ne_bot <| by simpa using hp.out.ne_zero

variable (K)

include hK in
theorem ncard_primesOver_of_prime_pow :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn this (𝓞 K) (K ≃ₐ[ℚ] K)
  have hζ := hK.zeta_spec
  have := liesOver_span_zeta_sub_one p k hζ
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) (K ≃ₐ[ℚ] K),
    inertiaDegIn_eq_inertiaDeg 𝒑 (span {hζ.toInteger - 1}) (K ≃ₐ[ℚ] K),
    inertiaDeg_span_zeta_sub_one,
    ramificationIdx_span_zeta_sub_one, mul_one, ← Nat.totient_prime_pow_succ hp.out,
    ← finrank _ K, IsGaloisGroup.card_eq_finrank (K ≃ₐ[ℚ] K) ℚ K, Nat.mul_eq_right] at h_main
  exact Module.finrank_pos.ne'

theorem eq_span_zeta_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  have : P ∈ primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} ∈ primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in
theorem inertiaDeg_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg 𝒑 P = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, inertiaDeg_span_zeta_sub_one]

include hK in
theorem ramificationIdx_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = p ^ k * (p - 1) := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, ramificationIdx_span_zeta_sub_one]

end PrimePow

section Prime

variable (p : ℕ) [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

instance isPrime_span_zeta_sub_one' : IsPrime (span {hζ.toInteger - 1}) := by
  rw [← pow_one p] at hK hζ
  exact isPrime_span_zeta_sub_one p 0 hζ

theorem inertiaDeg_span_zeta_sub_one' : inertiaDeg 𝒑 (span {hζ.toInteger - 1}) = 1 := by
  rw [← pow_one p] at hK hζ
  exact inertiaDeg_span_zeta_sub_one p 0 hζ

theorem ramificationIdx_span_zeta_sub_one' :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 (span {hζ.toInteger - 1}) = p - 1 := by
  rw [← pow_one p] at hK hζ
  rw [ramificationIdx_span_zeta_sub_one p 0 hζ, pow_zero, one_mul]

variable (K)

include hK in
theorem ncard_primesOver_of_prime :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  rw [← pow_one p] at hK
  exact ncard_primesOver_of_prime_pow p 0 K

theorem eq_span_zeta_sub_one_of_liesOver' (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  rw [← pow_one p] at hK hζ
  exact eq_span_zeta_sub_one_of_liesOver p 0 K hζ P

include hK in
theorem inertiaDeg_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg 𝒑 P = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P, inertiaDeg_span_zeta_sub_one']

include hK in
theorem ramificationIdx_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = p - 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P, ramificationIdx_span_zeta_sub_one']

end Prime

end IsCyclotomicExtension.Rat
