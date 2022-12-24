/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Notation
import Std.Data.Nat.Lemmas
import Std.Data.List.Basic
/-!
Definitions for `List` not (yet) in `Std`
-/


open Decidable List

universe u v w

namespace List



open Option Nat

#align list.nth List.get?

/-- nth element of a list `l` given `n < l.length`. -/
@[deprecated get]
def nthLe (l : List α) (n) (h : n < l.length) : α := get l ⟨n, h⟩
#align list.nth_le List.nthLe

set_option linter.deprecated false in
@[deprecated]
theorem nthLe_eq (l : List α) (n) (h : n < l.length) : nthLe l n h = get l ⟨n, h⟩ := rfl

/-- The head of a list, or the default element of the type is the list is `nil`. -/
@[simp] def headI [Inhabited α] : List α → α
| []       => default
| (a :: _) => a
#align list.head List.headI

#align list.map₂ List.zipWith

#noalign list.map_with_index_core
#align list.map_with_index List.mapIdx

/-- Find index of element with given property. -/
@[deprecated findIdx]
def findIndex (p : α → Prop) [DecidablePred p] : List α → ℕ := List.findIdx p
#align list.find_index List.findIndex

#align list.update_nth List.set

/-- Big or of a list of Booleans. -/
def bor (l : List Bool) : Bool :=
  any l id
#align list.bor List.bor

/-- Big and of a list of Booleans. -/
def band (l : List Bool) : Bool :=
  all l id
#align list.band List.band

/-- List consisting of an element `a` repeated a specified number of times. -/
@[simp]
def «repeat» (a : α) : Nat → List α
  | 0 => []
  | succ n => a :: «repeat» a n
#align list.repeat List.repeat

/-- The last element of a non-empty list. -/
def last : ∀ l : List α, l ≠ [] → α
  | [], h => absurd rfl h
  | [a], _ => a
  | _ :: b :: l, _ => last (b :: l) fun h => List.noConfusion h
#align list.last List.last

/-- The last element of a list, with the default if list empty -/
def ilast [Inhabited α] : List α → α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => ilast l
#align list.ilast List.ilast

/-- Initial segment of a list, i.e., with the last element dropped. -/
def init : List α → List α
  | [] => []
  | [_] => []
  | a :: l => a :: init l
#align list.init List.init

/-- List with a single given element. -/
@[inline]
protected def ret {α : Type u} (a : α) : List α :=
  [a]
#align list.ret List.ret

/-- `≤` implies not `>` for lists. -/
theorem le_eq_not_gt [LT α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬l₂ < l₁ := fun _ _ => rfl
#align list.le_eq_not_gt List.le_eq_not_gt


end List
