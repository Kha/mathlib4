/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.quotient
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Basic

/-!
# Quotients of families indexed by a finite type

This file provides `quotient.fin_choice`, a mechanism to go from a finite family of quotients
to a quotient of finite families.

## Main definitions

* `quotient.fin_choice`

-/


/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def Quotient.finChoiceAux {ι : Type _} [DecidableEq ι] {α : ι → Type _} [S : ∀ i, Setoid (α i)] :
    ∀ l : List ι, (∀ i ∈ l, Quotient (S i)) → @Quotient (∀ i ∈ l, α i) (by infer_instance)
  | [], _ => ⟦fun i hi => False.elim <| (List.mem_nil_iff i).mp hi⟧
  | i :: l, f =>
    by
    refine'
      Quotient.liftOn₂ (f i (List.mem_cons_self _ _))
        (Quotient.finChoiceAux l fun j h => f j (List.mem_cons_of_mem _ h)) _ _
    exact fun a l =>
      ⟦fun j h =>
        if e : j = i
        then by rw [e]; exact a
        else l _ ((List.mem_cons.mp h).resolve_left e)⟧
    refine' fun a₁ l₁ a₂ l₂ h₁ h₂ => Quotient.sound fun j h => _
    by_cases e : j = i <;> simp [e]
    · subst j
      exact h₁
    · exact h₂ _ _
#align quotient.fin_choice_aux Quotient.finChoiceAux

theorem Quotient.finChoiceAux_eq {ι : Type _} [DecidableEq ι] {α : ι → Type _}
    [S : ∀ i, Setoid (α i)] :
    ∀ (l : List ι) (f : ∀ i ∈ l, α i), (Quotient.finChoiceAux l fun i h => ⟦f i h⟧) = ⟦f⟧
  | [], f => Quotient.sound fun i h => ((List.mem_nil_iff i).mp h).elim
  | i :: l, f => by
    simp [Quotient.finChoiceAux, Quotient.finChoiceAux_eq l]
    refine' fun j h => _
    by_cases e : j = i <;> simp [e]
    subst j
    simp only [cast_eq]
    convert Setoid.refl (f i h)
    exact Setoid.refl _
#align quotient.fin_choice_aux_eq Quotient.finChoiceAux_eq

/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def Quotient.finChoice {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _}
    [S : ∀ i, Setoid (α i)] (f : ∀ i, Quotient (S i)) : @Quotient (∀ i, α i) (by infer_instance) :=
  Quotient.liftOn
    (@Quotient.recOn _ _ (fun l : Multiset ι => @Quotient (∀ i ∈ l, α i) (by infer_instance))
      Finset.univ.1 (fun l => Quotient.finChoiceAux l fun i _ => f i) fun a b h =>
      by
      have := fun a => Quotient.finChoiceAux_eq a fun i h => Quotient.out (f i)
      simp [Quotient.out_eq] at this
      simp [this]
      let g := fun a : Multiset ι =>
        Quotient.mk inferInstance (fun (i : ι) (h : i ∈ a) => Quotient.out (f i))
      simp only
      refine' eq_of_heq _
      refine' HEq.trans (eqRec_heq' _ _ : HEq _ (g a)) (_ : HEq (g a) (g b))
      congr 1; exact Quotient.sound h)
    (fun f => ⟦fun i => f i (Finset.mem_univ _)⟧) fun a b h => Quotient.sound fun i => by
      apply h
#align quotient.fin_choice Quotient.finChoice

/- Has an error in the motive for Quotient.inductionOn:

application type mismatch
  f i (_ : i ∈ Finset.univ)
argument has type
  i ∈ Finset.univ
but function has type
  i ∈ x✝ → α i
-/
theorem Quotient.finChoice_eq {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _}
    [∀ i, Setoid (α i)] (f : ∀ i, α i) : (Quotient.finChoice fun i => ⟦f i⟧) = ⟦f⟧ := by
  simp only [Quotient.finChoice, Quotient.finChoiceAux_eq]
  exact Quotient.inductionOn Finset.univ.val fun l => Quotient.sound (Setoid.refl _)

  done

#align quotient.fin_choice_eq Quotient.finChoice_eq
