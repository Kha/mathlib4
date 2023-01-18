/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.finset.pi
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.Multiset.Pi

/-!
# The cartesian product of finsets
-/


namespace Finset

open Multiset

/-! ### pi -/


section Pi

variable {α : Type _}

/-- The empty dependent product function, defined on the empty set. The assumption `a ∈ ∅` is never
satisfied. -/
def Pi.empty (β : α → Sort _) (a : α) (h : a ∈ (∅ : Finset α)) : β a :=
  Multiset.Pi.empty β a h
#align finset.pi.empty Finset.Pi.empty

variable {δ : α → Type _} [DecidableEq α]

/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
--Porting note: marked noncomputable
def pi (s : Finset α) (t : ∀ a, Finset (δ a)) : Finset (∀ a ∈ s, δ a) :=
  ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩
#align finset.pi Finset.pi

@[simp]
theorem pi_val (s : Finset α) (t : ∀ a, Finset (δ a)) : (s.pi t).1 = s.1.pi fun a => (t a).1 :=
  rfl
#align finset.pi_val Finset.pi_val

@[simp]
theorem mem_pi {s : Finset α} {t : ∀ a, Finset (δ a)} {f : ∀ a ∈ s, δ a} :
    f ∈ s.pi t ↔ ∀ (a) (h : a ∈ s), f a h ∈ t a :=
  Multiset.mem_pi _ _ _
#align finset.mem_pi Finset.mem_pi

/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
def pi.cons (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) :
    δ a' :=
  Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)
#align finset.pi.cons Finset.pi.cons

@[simp]
theorem pi.cons_same (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (h : a ∈ insert a s) :
    pi.cons s a b f a h = b :=
  Multiset.Pi.cons_same _
#align finset.pi.cons_same Finset.pi.cons_same

theorem pi.cons_ne {s : Finset α} {a a' : α} {b : δ a} {f : ∀ a, a ∈ s → δ a} {h : a' ∈ insert a s}
    (ha : a ≠ a') : pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
  Multiset.Pi.cons_ne _ (Ne.symm ha)
#align finset.pi.cons_ne Finset.pi.cons_ne

theorem pi_cons_injective {a : α} {b : δ a} {s : Finset α} (hs : a ∉ s) :
    Function.Injective (pi.cons s a b) := fun e₁ e₂ eq =>
  @Multiset.pi_cons_injective α _ δ a b s.1 hs _ _ <|
    funext fun e =>
      funext fun h =>
        have :
          pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using h) =
            pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using h) :=
          by rw [eq]
        this
#align finset.pi_cons_injective Finset.pi_cons_injective

@[simp]
theorem pi_empty {t : ∀ a : α, Finset (δ a)} : pi (∅ : Finset α) t = singleton (Pi.empty δ) :=
  rfl
#align finset.pi_empty Finset.pi_empty

@[simp]
theorem pi_insert [∀ a, DecidableEq (δ a)] {s : Finset α} {t : ∀ a : α, Finset (δ a)} {a : α}
    (ha : a ∉ s) : pi (insert a s) t = (t a).bunionᵢ fun b => (pi s t).image (pi.cons s a b) :=
  by
  apply eq_of_veq
  rw [← (pi (insert a s) t).2.dedup]
  refine'
    (fun s' (h : s' = a ::ₘ s.1) =>
        (_ :
          dedup (Multiset.pi s' fun a => (t a).1) =
            dedup
              ((t a).1.bind fun b =>
                dedup <|
                  (Multiset.pi s.1 fun a : α => (t a).val).map fun f a' h' =>
                    Multiset.Pi.cons s.1 a b f a' (h ▸ h'))))
      _ (insert_val_of_not_mem ha)
  subst s'; rw [pi_cons]
  congr ; funext b
  exact ((pi s t).nodup.map <| Multiset.pi_cons_injective ha).dedup.symm
#align finset.pi_insert Finset.pi_insert

theorem pi_singletons {β : Type _} (s : Finset α) (f : α → β) :
    (s.pi fun a => ({f a} : Finset β)) = {fun a _ => f a} :=
  by
  rw [eq_singleton_iff_unique_mem]
  constructor
  · simp
  intro a ha
  ext (i hi)
  rw [mem_pi] at ha
  simpa using ha i hi
#align finset.pi_singletons Finset.pi_singletons

theorem pi_const_singleton {β : Type _} (s : Finset α) (i : β) :
    (s.pi fun _ => ({i} : Finset β)) = {fun _ _ => i} :=
  pi_singletons s fun _ => i
#align finset.pi_const_singleton Finset.pi_const_singleton

theorem pi_subset {s : Finset α} (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) :
    s.pi t₁ ⊆ s.pi t₂ := fun _ hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)
#align finset.pi_subset Finset.pi_subset

theorem pi_disjoint_of_disjoint {δ : α → Type _} {s : Finset α} (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (ha : a ∈ s) (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha) <|
      congr_fun (congr_fun eq₁₂ a) ha
#align finset.pi_disjoint_of_disjoint Finset.pi_disjoint_of_disjoint

end Pi

end Finset
