/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Neighborhoods

/-!
# Open covers

We define `IsOpenCover` as a predicate on indexed families of open sets in a topological space `X`,
asserting that their union is `X`. This is an example of a declaration whose name is actually
longer than its content; but giving it a name serves as a way of standardizing API.
-/

@[expose] public section

open Set Topology

namespace TopologicalSpace

/-- An indexed family of open sets whose union is `X`. -/
def IsOpenCover {ι X : Type*} [TopologicalSpace X] (u : ι → Opens X) : Prop :=
  iSup u = ⊤

variable {ι κ X Y : Type*} [TopologicalSpace X] {u : ι → Opens X}
  [TopologicalSpace Y] {v : κ → Opens Y}

namespace IsOpenCover

lemma mk (h : iSup u = ⊤) : IsOpenCover u := h

lemma of_sets {v : ι → Set X} (h_open : ∀ i, IsOpen (v i)) (h_iUnion : ⋃ i, v i = univ) :
    IsOpenCover (fun i ↦ ⟨v i, h_open i⟩) := by
  simp [IsOpenCover, h_iUnion]

lemma iSup_eq_top (hu : IsOpenCover u) : ⨆ i, u i = ⊤ := hu

lemma iSup_set_eq_univ (hu : IsOpenCover u) : ⋃ i, (u i : Set X) = univ := by
  simpa [← SetLike.coe_set_eq] using hu.iSup_eq_top

/-- Pullback of a covering of `Y` by a continuous map `X → Y`, giving a covering of `X` with the
same index type. -/
lemma comap (hv : IsOpenCover v) (f : C(X, Y)) : IsOpenCover fun k ↦ (v k).comap f :=
  by simp [IsOpenCover, ← preimage_iUnion, hv.iSup_set_eq_univ]

lemma exists_mem (hu : IsOpenCover u) (a : X) : ∃ i, a ∈ u i := by
  simpa [← hu.iSup_set_eq_univ] using mem_univ a

lemma exists_mem_nhds (hu : IsOpenCover u) (a : X) : ∃ i, (u i : Set X) ∈ 𝓝 a :=
  match hu.exists_mem a with | ⟨i, hi⟩ => ⟨i, (u i).isOpen.mem_nhds hi⟩

lemma iUnion_inter (hu : IsOpenCover u) (s : Set X) :
    ⋃ i, s ∩ u i = s := by
  simp [← inter_iUnion, hu.iSup_set_eq_univ]

lemma isTopologicalBasis (hu : IsOpenCover u)
    {B : ∀ i, Set (Set (u i))} (hB : ∀ i, IsTopologicalBasis (B i)) :
    IsTopologicalBasis (⋃ i, (Subtype.val '' ·) '' B i) :=
  isTopologicalBasis_of_cover (fun i ↦ (u i).2) hu.iSup_set_eq_univ hB

end IsOpenCover

end TopologicalSpace
