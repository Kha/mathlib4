/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Core
import Mathlib.Algebra.GroupPower.Lemmas
import Qq.Match

/-!
## `norm_num` basic plugins

This file adds `norm_num` plugins for `+`, `*` and `^` along with other basic operations.
-/

namespace Mathlib
open Lean Meta

namespace Meta.NormNum
open Qq

theorem isNat_zero (α) [AddMonoidWithOne α] : IsNat (Zero.zero : α) (nat_lit 0) :=
  ⟨Nat.cast_zero.symm⟩

/-- The `norm_num` extension which identifies the expression `Zero.zero`, returning `0`. -/
@[norm_num Zero.zero] def evalZero : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Zero.zero) => return (.isNat sα (mkRawNatLit 0) q(isNat_zero $α) : Result q(Zero.zero))

theorem isNat_one (α) [AddMonoidWithOne α] : IsNat (One.one : α) (nat_lit 1) := ⟨Nat.cast_one.symm⟩

/-- The `norm_num` extension which identifies the expression `One.one`, returning `1`. -/
@[norm_num One.one] def evalOne : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(One.one) => return (.isNat sα (mkRawNatLit 1) q(isNat_one $α) : Result q(One.one))

theorem isNat_ofNat (α : Type u_1) [AddMonoidWithOne α] {a : α} {n : ℕ}
    (h : n = a) : IsNat a n := ⟨h.symm⟩

/-- The `norm_num` extension which identifies an expression `OfNat.ofNat n`, returning `n`. -/
@[norm_num OfNat.ofNat _] def evalOfNat : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(@OfNat.ofNat _ $n $oα) =>
    let n : Q(ℕ) ← whnf n
    guard n.isNatLit
    let ⟨a, (pa : Q($n = $e))⟩ ← mkOfNat α sα n
    guard <|← isDefEq a e
    return .isNat sα n (q(isNat_ofNat $α $pa) : Expr)

theorem isNat_cast {R} [AddMonoidWithOne R] (n m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Nat.cast n`, returning `n`. -/
@[norm_num Nat.cast _] def evalNatCast : NormNumExt where eval {u α} e := do
  let sα ← inferAddMonoidWithOne α
  match e with
  | ~q(Nat.cast $a) =>
    let ⟨na, pa⟩ ← deriveNat a q(instAddMonoidWithOneNat)
    let pa : Q(IsNat $a $na) := pa
    return (.isNat sα na q(@isNat_cast $α _ $a $na $pa) : Result q(Nat.cast $a : $α))

theorem isNat_int_cast {R} [Ring R] (n : ℤ) (m : ℕ) :
    IsNat n m → IsNat (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_cast {R} [Ring R] (n m : ℤ) :
    IsInt n m → IsInt (n : R) m := by rintro ⟨⟨⟩⟩; exact ⟨rfl⟩

/-- The `norm_num` extension which identifies an expression `Int.cast n`, returning `n`. -/
@[norm_num Int.cast _] def evalIntCast : NormNumExt where eval {u α} e := do
  let rα ← inferRing α
  match e with
  | ~q(Int.cast $a) =>
    match ← derive (α := q(ℤ)) a with
    | .isNat _ na pa =>
      let sα : Q(AddMonoidWithOne $α) := q(instAddMonoidWithOne)
      let pa : Q(@IsNat _ instAddMonoidWithOne $a $na) := pa
      return (.isNat sα na q(@isNat_int_cast $α _ $a $na $pa) : Result q(Int.cast $a : $α))
    | .isNegNat _ na pa =>
      let pa : Q(@IsInt _ instRingInt $a (.negOfNat $na)) := pa
      return (.isNegNat rα na q(isInt_cast $a (.negOfNat $na) $pa) : Result q(Int.cast $a : $α))
    | _ => failure

theorem isNat_add {α} [AddMonoidWithOne α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.add a' b' = c → IsNat (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_add _ _).symm⟩

theorem isInt_add {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.add a' b' = c → IsInt (a + b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_add ..).symm⟩

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
def invertibleOfMul {α} [Semiring α] (k : ℕ) (b : α) :
    ∀ (a : α) [Invertible a], a = k * b → Invertible b
  | _, ⟨c, hc1, hc2⟩, rfl => by
    rw [← mul_assoc] at hc1
    rw [Nat.cast_commute k, mul_assoc, Nat.cast_commute k] at hc2
    exact ⟨_, hc1, hc2⟩

/-- If `b` divides `a` and `a` is invertible, then `b` is invertible. -/
def invertibleOfMul' {α} [Semiring α] {a k b : ℕ} [Invertible (a : α)]
    (h : a = k * b) : Invertible (b : α) := invertibleOfMul k (b:α) ↑a (by simp [h])

-- TODO: clean up and move it somewhere in mathlib? It's a bit much for this file
theorem isRat_add {α} [Ring α] {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    IsRat a na da → IsRat b nb db →
    Int.add (Int.mul na db) (Int.mul nb da) = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (a + b) nc dc := by
  rintro ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * db + nb * da = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  use this
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (↑· * (⅟↑da * ⅟↑db : α)) h₁
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, ← mul_assoc,
    add_mul, mul_mul_invOf_self_cancel] at h₁
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp [← mul_assoc, H] at h₁ h₂; rw [h₁, h₂, Nat.cast_commute]
  simp only [mul_mul_invOf_self_cancel,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

instance : MonadLift Option MetaM where
  monadLift
  | none => failure
  | some e => pure e

/-- The `norm_num` extension which identifies expressions of the form `a + b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ + _, Add.add _ _] def evalAdd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let ra ← derive a; let rb ← derive b
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ .. | .isNat _ .., .isRat _ ..
  | .isNegNat _ .., .isNat _ .. | .isNegNat _ .., .isNegNat _ .. | .isNegNat _ .., .isRat _ ..
  | .isRat _ .., .isNat _ .. | .isRat _ .., .isNegNat _ .. | .isRat _ .., .isRat _ .. =>
    guard <|← withNewMCtxDepth <| isDefEq f q(HAdd.hAdd (α := $α))
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za + zb
      have c := mkRawIntLit zc
      let r : Q(Int.add $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc q(isInt_add $pa $pb $r) : Result q($a + $b))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
      let qc := qa + qb
      let dd := qa.den * qb.den
      let k := dd / qc.den
      have t1 : Q(ℤ) := mkRawIntLit (k * qc.num)
      have t2 : Q(ℕ) := mkRawNatLit dd
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have k : Q(ℕ) := mkRawNatLit k
      let r1 : Q(Int.add (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
        (q(Eq.refl $t1) : Expr)
      let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
      return (.isRat dα qc nc dc q(isRat_add $pa $pb $r1 $r2) : Result q($a + $b))
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
    | .isNat _ na pa, .isNat sα nb pb =>
      have pa : Q(IsNat $a $na) := pa
      have c : Q(ℕ) := mkRawNatLit (na.natLit! + nb.natLit!)
      let r : Q(Nat.add $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat sα c q(isNat_add $pa $pb $r) : Result q($a + $b))
  core

theorem isInt_neg {α} [Ring α] : {a : α} → {a' b : ℤ} →
    IsInt a a' → Int.neg a' = b → IsInt (-a) b
  | _, _, _, ⟨rfl⟩, rfl => ⟨(Int.cast_neg ..).symm⟩

theorem isRat_neg {α} [Ring α] : {a : α} → {n n' : ℤ} → {d : ℕ} →
    IsRat a n d → Int.neg n = n' → IsRat (-a) n' d
  | _, _, _, _, ⟨h, rfl⟩, rfl => ⟨h, by rw [← neg_mul, ← Int.cast_neg]; rfl⟩

/-- The `norm_num` extension which identifies expressions of the form `-a`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num -_] def evalNeg : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let rα ← inferRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(Neg.neg (α := $α))
  let rec
  /-- Main part of `evalNeg`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt
      let zb := -za
      have b := mkRawIntLit zb
      let r : Q(Int.neg $na = $b) := (q(Eq.refl $b) : Expr)
      return (.isInt rα b zb q(isInt_neg $pa $r) : Result q(-$a))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := by clear rα; exact do
      let ⟨qa, na, da, pa⟩ ← ra.toRat'
      let qb := -qa
      have nb := mkRawIntLit qb.num
      let r : Q(Int.neg $na = $nb) := (q(Eq.refl $nb) : Expr)
      return (.isRat' dα qb nb da q(isRat_neg $pa $r) : Result q(-$a))
    match ra with
    | .isBool _ .. => failure
    | .isNat _ .. => intArm rα
    | .isNegNat rα .. => intArm rα
    | .isRat dα .. => ratArm dα
  core

theorem isInt_sub {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.sub a' b' = c → IsInt (a - b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_sub ..).symm⟩

theorem isRat_sub {α} [Ring α] {a b : α} {na nb nc : ℤ} {da db dc k : ℕ}
    (ra : IsRat a na da) (rb : IsRat b nb db)
    (h₁ : Int.sub (Int.mul na db) (Int.mul nb da) = Int.mul k nc)
    (h₂ : Nat.mul da db = Nat.mul k dc) :
    IsRat (a - b) nc dc := by
  rw [sub_eq_add_neg]
  refine isRat_add ra (isRat_neg (n' := -nb) rb rfl) (k := k) (nc := nc) ?_ h₂
  rw [show Int.mul (-nb) _ = _ from neg_mul ..]; exact h₁

/-- The `norm_num` extension which identifies expressions of the form `a - b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ - _, Sub.sub _ _] def evalSub : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let ra ← derive a; let rb ← derive b
  let rα ← inferRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(HSub.hSub (α := $α))
  let rec
  /-- Main part of `evalAdd`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za - zb
      have c := mkRawIntLit zc
      let r : Q(Int.sub $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc q(isInt_sub $pa $pb $r) : Result q($a - $b))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := by clear rα; exact do
      let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
      let qc := qa - qb
      let dd := qa.den * qb.den
      let k := dd / qc.den
      have t1 : Q(ℤ) := mkRawIntLit (k * qc.num)
      have t2 : Q(ℕ) := mkRawNatLit dd
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have k : Q(ℕ) := mkRawNatLit k
      let r1 : Q(Int.sub (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
        (q(Eq.refl $t1) : Expr)
      let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
      return (.isRat dα qc nc dc q(isRat_sub $pa $pb $r1 $r2) : Result q($a - $b))
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα ..
    | .isNat _ .., .isNat _ .. => intArm rα
  core

theorem isNat_mul {α} [Semiring α] : {a b : α} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.mul a' b' = c → IsNat (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Nat.cast_mul ..).symm⟩

theorem isInt_mul {α} [Ring α] : {a b : α} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.mul a' b' = c → IsInt (a * b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨(Int.cast_mul ..).symm⟩

theorem isRat_mul {α} [Ring α] {a b : α} {na nb nc : ℤ} {da db dc k : ℕ} :
    IsRat a na da → IsRat b nb db →
    Int.mul na nb = Int.mul k nc →
    Nat.mul da db = Nat.mul k dc →
    IsRat (a * b) nc dc := by
  rintro ⟨_, rfl⟩ ⟨_, rfl⟩ (h₁ : na * nb = k * nc) (h₂ : da * db = k * dc)
  have : Invertible (↑(da * db) : α) := by simpa using invertibleMul (da:α) db
  have := invertibleOfMul' (α := α) h₂
  refine ⟨this, ?_⟩
  have H := (Nat.cast_commute (α := α) da db).invOf_left.invOf_right.right_comm
  have h₁ := congr_arg (Int.cast (R := α)) h₁
  simp only [Int.cast_mul, Int.cast_ofNat] at h₁
  simp [← mul_assoc, (Nat.cast_commute (α := α) da nb).invOf_left.right_comm, h₁]
  have h₂ := congr_arg (↑nc * ↑· * (⅟↑da * ⅟↑db * ⅟↑dc : α)) h₂
  simp [← mul_assoc] at h₂; rw [H] at h₂
  simp [mul_mul_invOf_self_cancel] at h₂; rw [h₂, Nat.cast_commute]
  simp only [mul_mul_invOf_self_cancel,
    (Nat.cast_commute (α := α) da dc).invOf_left.invOf_right.right_comm,
    (Nat.cast_commute (α := α) db dc).invOf_left.invOf_right.right_comm]

/-- The `norm_num` extension which identifies expressions of the form `a * b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ * _, Mul.mul _ _] def evalMul : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let sα ← inferSemiring α
  let ra ← derive a; let rb ← derive b
  guard <|← withNewMCtxDepth <| isDefEq f q(HMul.hMul (α := $α))
  let rec
  /-- Main part of `evalMul`. -/
  core : Option (Result e) := do
    let intArm (rα : Q(Ring $α)) := do
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      let zc := za * zb
      have c := mkRawIntLit zc
      let r : Q(Int.mul $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc (q(isInt_mul $pa $pb $r) : Expr) : Result q($a * $b))
    let ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
      let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
      let qc := qa * qb
      let dd := qa.den * qb.den
      let k := dd / qc.den
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have k : Q(ℕ) := mkRawNatLit k
      let r1 : Q(Int.mul $na $nb = Int.mul $k $nc) :=
        (q(Eq.refl (Int.mul $na $nb)) : Expr)
      have t2 : Q(ℕ) := mkRawNatLit dd
      let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
      return (.isRat dα qc nc dc q(isRat_mul $pa $pb $r1 $r2) : Result q($a * $b))
    match ra, rb with
    | .isBool .., _ | _, .isBool .. => failure
    | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
    | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
    | .isNat _ na pa, .isNat mα nb pb =>
      let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
      let pb : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $b $nb) := pb
      have c : Q(ℕ) := mkRawNatLit (na.natLit! * nb.natLit!)
      let r : Q(Nat.mul $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isNat mα c (q(isNat_mul (α := $α) $pa $pb $r) : Expr) : Result q($a * $b))
  core

theorem isNat_pow {α} [Semiring α] : {a : α} → {b a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.pow a' b' = c → IsNat (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

theorem isInt_pow {α} [Ring α] : {a : α} → {b : ℕ} → {a' : ℤ} → {b' : ℕ} → {c : ℤ} →
    IsInt a a' → IsNat b b' → Int.pow a' b' = c → IsInt (a ^ b) c
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by simp⟩

theorem isRat_pow {α} [Ring α] {a : α} {an cn : ℤ} {ad b b' cd : ℕ} :
    IsRat a an ad → IsNat b b' →
    Int.pow an b' = cn → Nat.pow ad b' = cd →
    IsRat (a ^ b) cn cd := by
  rintro ⟨_, rfl⟩ ⟨rfl⟩ (rfl : an ^ b = _) (rfl : ad ^ b = _)
  have := invertiblePow (ad:α) b
  rw [← Nat.cast_pow] at this
  use this; simp [invOf_pow, Commute.mul_pow]

/-- The `norm_num` extension which identifies expressions of the form `a ^ b`,
such that `norm_num` successfully recognises both `a` and `b`, with `b : ℕ`. -/
@[norm_num (_ : α) ^ (_ : ℕ), Pow.pow _ (_ : ℕ)]
def evalPow : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q(ℕ)) ← whnfR e | failure
  let ⟨nb, pb⟩ ← deriveNat b q(instAddMonoidWithOneNat)
  let sα ← inferSemiring α
  let ra ← derive a
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(HPow.hPow (α := $α))
  let rec
  /-- Main part of `evalPow`. -/
  core : Option (Result e) := do
    match ra with
    | .isBool .. => failure
    | .isNat sα na pa =>
      let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
      have c : Q(ℕ) := mkRawNatLit (na.natLit! ^ nb.natLit!)
      let r : Q(Nat.pow $na $nb = $c) := (q(Eq.refl $c) : Expr)
      let pb : Q(IsNat $b $nb) := pb
      return (.isNat sα c (q(isNat_pow $pa $pb $r) : Expr) : Result q($a ^ $b))
    | .isNegNat rα .. =>
      let ⟨za, na, pa⟩ ← ra.toInt
      let zc := za ^ nb.natLit!
      let c := mkRawIntLit zc
      let r : Q(Int.pow $na $nb = $c) := (q(Eq.refl $c) : Expr)
      return (.isInt rα c zc (q(isInt_pow $pa $pb $r) : Expr) : Result q($a ^ $b))
    | .isRat dα qa na da pa =>
      let qc := qa ^ nb.natLit!
      have nc : Q(ℤ) := mkRawIntLit qc.num
      have dc : Q(ℕ) := mkRawNatLit qc.den
      have r1 : Q(Int.pow $na $nb = $nc) := (q(Eq.refl $nc) : Expr)
      have r2 : Q(Nat.pow $da $nb = $dc) := (q(Eq.refl $dc) : Expr)
      return (.isRat dα qc nc dc (q(isRat_pow $pa $pb $r1 $r2) : Expr) : Result q($a ^ $b))
  core

theorem isRat_inv_pos {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.ofNat (Nat.succ n)) d → IsRat a⁻¹ (.ofNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  refine ⟨this, by simp⟩

theorem isRat_inv_zero {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 0) → IsNat a⁻¹ (nat_lit 0)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_neg {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.negOfNat (Nat.succ n)) d → IsRat a⁻¹ (.negOfNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_coe, Int.cast_neg,
    Int.cast_ofNat, invOf_eq_inv, inv_neg,  neg_mul, mul_inv_rev, inv_inv]

/-- The `norm_num` extension which identifies expressions of the form `a⁻¹`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(Inv.inv (α := $α))
  let ⟨qa, na, da, pa⟩ ← ra.toRat'
  let qb := qa⁻¹
  if qa > 0 then
    -- instead of inferCharZeroOfRing (q(DivisionRing.toRing) : Q(Ring $α))
    let _i ← inferCharZeroOfDivisionRing dα
    have lit : Q(ℕ) := na.appArg!
    have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
    let pa : Q(IsRat «$a» (Int.ofNat (Nat.succ $lit2)) $da) := pa
    return (.isRat' dα qb q(.ofNat $da) lit
      (q(isRat_inv_pos (α := $α) $pa) : Expr) : Result q($a⁻¹))
  else if qa < 0 then
    let _i ← inferCharZeroOfDivisionRing dα
    have lit : Q(ℕ) := na.appArg!
    have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
    let pa : Q(IsRat «$a» (Int.negOfNat (Nat.succ $lit2)) $da) := pa
    return (.isRat' dα qb q(.negOfNat $da) lit
      (q(isRat_inv_neg (α := $α) $pa) : Expr) : Result q($a⁻¹))
  else
    let .isNat inst _z (pa : Q(@IsNat _ AddGroupWithOne.toAddMonoidWithOne $a (nat_lit 0))) := ra
      | failure
    return (.isNat inst _z (q(isRat_inv_zero $pa) : Expr) : Result q($a⁻¹))

theorem isRat_div [DivisionRing α] : {a b : α} → {cn : ℤ} → {cd : ℕ} → IsRat (a * b⁻¹) cn cd →
    IsRat (a / b) cn cd
  | _, _, _, _, h => by simp [div_eq_mul_inv]; exact h

/-- The `norm_num` extension which identifies expressions of the form `a / b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ / _, Div.div _ _] def evalDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := $α))
  let rab ← derive (q($a * $b⁻¹) : Q($α))
  let ⟨qa, na, da, pa⟩ ← rab.toRat'
  let pa : Q(IsRat ($a * $b⁻¹) $na $da) := pa
  return (.isRat' dα qa na da q(isRat_div $pa) : Result q($a / $b))

/-
# Logic
-/

/-- The `norm_num` extension which identifies `True`. -/
@[norm_num True] def evalTrue : NormNumExt where eval {u α} e := do
  let .const ``True _ ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq α q(Prop)
  return (.isTrue q(True.intro) : Result q(True))

/-- The `norm_num` extension which identifies expressions of the form `¬a`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num ¬_] def evalNot : NormNumExt where eval {u α} e := do
  let .app (.const ``Not _) (a : Q($α)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq α q(Prop)
  let .isBool b p ← derive a | failure
  have a : Q(Prop) := a
  if b then
    have p : Q($a) := p
    return (.isFalse q(not_not_intro $p) : Result q(¬$a))
  else
    have p : Q(¬$a) := p
    return (.isTrue q($p) : Result q(¬$a))

/-
# (In)equalities
-/

theorem isNat_eq_true [AddMonoidWithOne α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.beq a' b' = true → a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simp; exact Nat.eq_of_beq_eq_true h

theorem isNat_le_true [OrderedSemiring α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble a' b' = true → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.mono_cast (Nat.le_of_ble_eq_true h)

theorem isNat_lt_true [OrderedSemiring α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble b' a' = false → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h =>
    Nat.cast_lt.2 <| Nat.not_le.1 <| Nat.not_le_of_not_ble_eq_true <| ne_true_of_eq_false h

theorem isNat_eq_false [AddMonoidWithOne α] [CharZero α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.beq a' b' = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simp; exact Nat.ne_of_beq_eq_false h

theorem isNat_le_false [OrderedSemiring α] [CharZero α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble a' b' = false) : ¬a ≤ b :=
  not_le_of_lt (isNat_lt_true hb ha h)

theorem isNat_lt_false [OrderedSemiring α] [CharZero α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble b' a' = true) : ¬a < b :=
  not_lt_of_le (isNat_le_true hb ha h)

--!! Does this belong here?
--!!Does it exist already? Is using `decide` just as good? Not sure what instances we have.
/-- Boolean equality for `ℤ` which uses bignum representation under the hood. -/
def _root_.Int.beq : (a b : ℤ) → Bool
| .ofNat na, .ofNat nb => Nat.beq na nb
| .negSucc na, .negSucc nb => Nat.beq na nb
| _, _ => false

theorem Int.eq_of_beq_eq_true : {n m : Int} → Eq (n.beq m) true → Eq n m
| .ofNat _, .ofNat _, h => congr_arg Int.ofNat <| Nat.eq_of_beq_eq_true h
| .negSucc _, .negSucc _, h => congr_arg Int.negSucc <| Nat.eq_of_beq_eq_true h
| .ofNat _, .negSucc _, _ => by contradiction
| .negSucc _, .ofNat _, _ => by contradiction

theorem Int.ne_of_beq_eq_false : {n m : Int} → Eq (n.beq m) false → Not (Eq n m)
| .ofNat _, .ofNat _, h => by have := Nat.ne_of_beq_eq_false h; simpa
| .negSucc _, .negSucc _, h => by have := Nat.ne_of_beq_eq_false h; simpa
| .ofNat _, .negSucc _, _ => fun.
| .negSucc _, .ofNat _, _ => fun.

theorem isInt_eq_true [Ring α] [CharZero α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → Int.beq a' b' = true → a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simp; exact Int.eq_of_beq_eq_true h

theorem isInt_le_true [OrderedRing α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' ≤ b') → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_mono <| of_decide_eq_true h

theorem isInt_lt_true [OrderedRing α] [Nontrivial α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' < b') → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_lt.2 <| of_decide_eq_true h

theorem isInt_eq_false [Ring α] [CharZero α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → Int.beq a' b' = false → ¬a = b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => by simp; exact Int.ne_of_beq_eq_false h

theorem isInt_le_false [OrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' < a')) : ¬a ≤ b :=
  not_le_of_lt (isInt_lt_true hb ha h)

theorem isInt_lt_false [OrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' ≤ a')) : ¬a < b :=
  not_lt_of_le (isInt_le_true hb ha h)

/-- Boolean equality for `ℚ` which uses bignum representation under the hood.

  This takes advantage of the fact that rationals are reduced. -/
def Rat.beq : ℚ → ℚ → Bool
| ⟨na, da, _, _⟩, ⟨nb, db, _, _⟩ => Int.beq na nb && Nat.beq da db

/-- Boolean equality for rationals represented as numerators and denominators. -/
def Rat.beq' (na : ℤ) (da : ℕ) (nb : ℤ) (db : ℕ) : Bool := Int.beq (na * db) (nb * da)

section
set_option warningAsError false -- FIXME: prove the sorries

--!! Does this need to be `DivisionRing α`?
theorem isRat_eq_true [Ring α] [CharZero α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → Rat.beq' na da nb db = true → a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by simp; have := Int.eq_of_beq_eq_true h; sorry

theorem isRat_eq_false [Ring α] [CharZero α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → Rat.beq' na da nb db = false → ¬a = b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by simp; have := Int.ne_of_beq_eq_false h; sorry

theorem isRat_le_true [OrderedRing α] : {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → decide (nb * da ≤ na * db) → a ≤ b
  | _, _, _, _, _, _, ⟨_, rfl⟩, ⟨_, rfl⟩, h => sorry
end
-- theorem isRat_lt_true [OrderedRing α] [Nontrivial α] : {a b : α} → {a' b' : ℤ} →
--     IsRat a a' → IsRat b b' → decide (a' < b') → a < b
--   | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_lt.2 <| of_decide_eq_true h

-- theorem isRat_le_false [OrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ}
--     (ha : IsRat a a') (hb : IsRat b b') (h : decide (b' < a')) : ¬a ≤ b :=
--   not_le_of_lt (isRat_lt_true hb ha h)

-- theorem isRat_lt_false [OrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ}
--     (ha : IsRat a a') (hb : IsRat b b') (h : decide (b' ≤ a')) : ¬a < b :=
--   not_lt_of_le (isRat_le_true hb ha h)

/-- The `norm_num` extension which identifies expressions of the form `a = b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ = _, Eq _ _] def evalEq : NormNumExt where eval {u α} e := do
  let .app (.app f a) b ← whnfR e | failure
  let ⟨.succ u, α, a⟩ ← inferTypeQ a | failure
  have b : Q($α) := b
  guard <|← withNewMCtxDepth <| isDefEq f q(Eq (α := $α))
  let ra ← derive a; let rb ← derive b
  let intArm (rα : Q(Ring $α)) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    if let .some _i ← inferCharZeroOfRing? rα then
      let ⟨za, na, pa⟩ ← ra.toInt; let ⟨zb, nb, pb⟩ ← rb.toInt
      if Int.beq za zb then
        let r : Q(Int.beq $na $nb = true) := (q(Eq.refl true) : Expr)
        return (.isTrue (q(isInt_eq_true $pa $pb $r) : Expr) : Result q($a = $b))
      else
        let r : Q(Int.beq $na $nb = false) := (q(Eq.refl false) : Expr)
        return (.isFalse (q(isInt_eq_false $pa $pb $r) : Expr) : Result q($a = $b))
    else
      failure --TODO: nonzero characteristic
  let ratArm (dα : Q(DivisionRing $α)) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    if let .some _i ← inferCharZeroOfDivisionRing? dα then
      let ⟨qa, na, da, pa⟩ ← ra.toRat'; let ⟨qb, nb, db, pb⟩ ← rb.toRat'
      if Rat.beq qa qb then
        let r : Q(Rat.beq' $na $da $nb $db = true) := (q(Eq.refl true) : Expr)
        return (.isTrue (q(isRat_eq_true $pa $pb $r) : Expr) : Result q($a = $b))
      else
        let r : Q(Rat.beq' $na $da $nb $db = false) := (q(Eq.refl false) : Expr)
        return (.isFalse (q(isRat_eq_false $pa $pb $r) : Expr) : Result q($a = $b))
    else
      failure --TODO: nonzero characteristic
  match ra, rb with
  | .isBool _ba _pa, .isBool _bb _pb => failure
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
  | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
  | .isNat _ na pa, .isNat _ nb pb =>
    let mα ← inferAddMonoidWithOne α  --!! Some subtleties with instance management to check.
    if let .some _i ← inferCharZeroOfAddMonoidWithOne? mα then
      let pa : Q(@IsNat _ $mα $a $na) := pa
      let pb : Q(@IsNat _ $mα $b $nb) := pb
      if na.natLit!.beq nb.natLit! then
        let r : Q(Nat.beq $na $nb = true) := (q(Eq.refl true) : Expr)
        return (.isTrue (q(isNat_eq_true $pa $pb $r) : Expr) : Result q($a = $b))
      else
        trace[Tactic.norm_num] "!! unequal"
        let r : Q(Nat.beq $na $nb = false) := (q(Eq.refl false) : Expr)
        return (.isFalse (q(isNat_eq_false $pa $pb $r) : Expr) : Result q($a = $b))
    else
      failure --TODO: nonzero characteristic


/-- The `norm_num` extension which identifies expressions of the form `a < b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num _ < _] def evalLT : NormNumExt where eval (e : Q(Prop)) := do
  let .app (.app f a) b ← whnfR e | failure
  let ⟨.succ u, α, a⟩ ← inferTypeQ a | failure
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let intArm (_ : Unit) : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    failure -- TODO
  let ratArm _ : MetaM (@Result _ (q(Prop) : Q(Type)) e) := do
    failure -- TODO
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isRat _ .., _ | _, .isRat _ .. => ratArm ()
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm ()
  | .isNat _ na pa, .isNat _ nb pb =>
    let _i ← inferOrderedSemiring α
    guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
    let _i ← synthInstanceQ (q(@CharZero $α AddCommMonoidWithOne.toAddMonoidWithOne) : Q(Prop))
    let pa : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $a $na) := pa
    let pb : Q(@IsNat _ AddCommMonoidWithOne.toAddMonoidWithOne $b $nb) := pb
    if na.natLit! < nb.natLit! then
      let r : Q(Nat.ble $nb $na = false) := (q(Eq.refl false) : Expr)
      return (.isTrue (q(isNat_lt_true $pa $pb $r) : Expr) : Result q($a < $b))
    else
      let r : Q(Nat.ble $nb $na = true) := (q(Eq.refl true) : Expr)
      return (.isFalse (q(isNat_lt_false $pa $pb $r) : Expr) : Result q($a < $b))
