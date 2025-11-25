/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Triangulated Categories

This file contains the definition of triangulated categories, which are
pretriangulated categories which satisfy the octahedron axiom.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

noncomputable section

namespace CategoryTheory

open Limits Category Preadditive Pretriangulated

open ZeroObject

variable (C : Type*) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

namespace Triangulated

variable {C}

/-- An octahedron is a type of datum whose existence is asserted by the octahedron axiom (TR 4). -/
@[stacks 05QK]
structure Octahedron
  {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C) where
  /-- `m₁` is the morphism `a` of (TR 4) as presented in Stacks. -/
  m₁ : Z₁₂ ⟶ Z₁₃
  /-- `m₃` is the morphism `b` of (TR 4) as presented in Stacks. -/
  m₃ : Z₁₃ ⟶ Z₂₃
  comm₁ : v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃
  comm₂ : m₁ ≫ w₁₃ = w₁₂
  comm₃ : v₁₃ ≫ m₃ = v₂₃
  comm₄ : w₁₃ ≫ u₁₂⟦1⟧' = m₃ ≫ w₂₃
  mem : Triangle.mk m₁ m₃ (w₂₃ ≫ v₁₂⟦1⟧') ∈ distTriang C

instance (X : C) :
    Nonempty (Octahedron (comp_id (𝟙 X)) (contractible_distinguished X)
      (contractible_distinguished X) (contractible_distinguished X)) := by
  refine ⟨⟨0, 0, ?_, ?_, ?_, ?_, isomorphic_distinguished _ (contractible_distinguished (0 : C)) _
    (Triangle.isoMk _ _ (by rfl) (by rfl) (by rfl))⟩⟩
  all_goals apply Subsingleton.elim

namespace Octahedron

attribute [reassoc] comm₁ comm₂ comm₃ comm₄

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} {comm : u₁₂ ≫ u₂₃ = u₁₃}
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C}
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C}
  (h : Octahedron comm h₁₂ h₂₃ h₁₃)

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an octahedron. -/
@[simps!]
def triangle : Triangle C :=
  Triangle.mk h.m₁ h.m₃ (w₂₃ ≫ v₁₂⟦1⟧')

/-- The first morphism of triangles given by an octahedron. -/
@[simps]
def triangleMorphism₁ : Triangle.mk u₁₂ v₁₂ w₁₂ ⟶ Triangle.mk u₁₃ v₁₃ w₁₃ where
  hom₁ := 𝟙 X₁
  hom₂ := u₂₃
  hom₃ := h.m₁
  comm₁ := by
    dsimp
    rw [id_comp, comm]
  comm₂ := h.comm₁
  comm₃ := by
    dsimp
    simpa only [Functor.map_id, comp_id] using h.comm₂.symm

/-- The second morphism of triangles given an octahedron. -/
@[simps]
def triangleMorphism₂ : Triangle.mk u₁₃ v₁₃ w₁₃ ⟶ Triangle.mk u₂₃ v₂₃ w₂₃ where
  hom₁ := u₁₂
  hom₂ := 𝟙 X₃
  hom₃ := h.m₃
  comm₁ := by
    dsimp
    rw [comp_id, comm]
  comm₂ := by
    dsimp
    rw [id_comp, h.comm₃]
  comm₃ := h.comm₄


variable (u₁₂ u₁₃ u₂₃ comm h₁₂ h₁₃ h₂₃)

/-- When two diagrams are isomorphic, an octahedron for one gives an octahedron for the other. -/
def ofIso {X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' : C} (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃') (u₁₃' : X₁' ⟶ X₃')
    (comm' : u₁₂' ≫ u₂₃' = u₁₃')
    (e₁ : X₁ ≅ X₁') (e₂ : X₂ ≅ X₂') (e₃ : X₃ ≅ X₃')
    (comm₁₂ : u₁₂ ≫ e₂.hom = e₁.hom ≫ u₁₂') (comm₂₃ : u₂₃ ≫ e₃.hom = e₂.hom ≫ u₂₃')
    (v₁₂' : X₂' ⟶ Z₁₂') (w₁₂' : Z₁₂' ⟶ X₁'⟦(1 : ℤ)⟧)
    (h₁₂' : Triangle.mk u₁₂' v₁₂' w₁₂' ∈ distTriang C)
    (v₂₃' : X₃' ⟶ Z₂₃') (w₂₃' : Z₂₃' ⟶ X₂'⟦(1 : ℤ)⟧)
    (h₂₃' : Triangle.mk u₂₃' v₂₃' w₂₃' ∈ distTriang C)
    (v₁₃' : X₃' ⟶ Z₁₃') (w₁₃' : Z₁₃' ⟶ X₁'⟦(1 : ℤ)⟧)
    (h₁₃' : Triangle.mk (u₁₃') v₁₃' w₁₃' ∈ distTriang C)
    (H : Octahedron comm' h₁₂' h₂₃' h₁₃') : Octahedron comm h₁₂ h₂₃ h₁₃ := by
  let iso₁₂ := isoTriangleOfIso₁₂ _ _ h₁₂ h₁₂' e₁ e₂ comm₁₂
  let iso₂₃ := isoTriangleOfIso₁₂ _ _ h₂₃ h₂₃' e₂ e₃ comm₂₃
  let iso₁₃ := isoTriangleOfIso₁₂ _ _ h₁₃ h₁₃' e₁ e₃ (by
    dsimp; rw [← comm, assoc, ← comm', ← reassoc_of% comm₁₂, comm₂₃])
  have eq₁₂ := iso₁₂.hom.comm₂
  have eq₁₂' := iso₁₂.hom.comm₃
  have eq₁₃ := iso₁₃.hom.comm₂
  have eq₁₃' := iso₁₃.hom.comm₃
  have eq₂₃ := iso₂₃.hom.comm₂
  have eq₂₃' := iso₂₃.hom.comm₃
  have rel₁₂ := H.triangleMorphism₁.comm₂
  have rel₁₃ := H.triangleMorphism₁.comm₃
  have rel₂₂ := H.triangleMorphism₂.comm₂
  have rel₂₃ := H.triangleMorphism₂.comm₃
  dsimp [iso₁₂, iso₂₃, iso₁₃] at eq₁₂ eq₁₂' eq₁₃ eq₁₃' eq₂₃ eq₂₃' rel₁₂ rel₁₃ rel₂₂ rel₂₃
  rw [Functor.map_id, comp_id] at rel₁₃
  rw [id_comp] at rel₂₂
  refine ⟨iso₁₂.hom.hom₃ ≫ H.m₁ ≫ iso₁₃.inv.hom₃,
    iso₁₃.hom.hom₃ ≫ H.m₃ ≫ iso₂₃.inv.hom₃, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reassoc_of% eq₁₂, ← cancel_mono iso₁₃.hom.hom₃, assoc, assoc, assoc, assoc,
      iso₁₃.inv_hom_id_triangle_hom₃, eq₁₃, reassoc_of% comm₂₃, ← rel₁₂]
    dsimp
    rw [comp_id]
  · rw [← cancel_mono (e₁.hom⟦(1 : ℤ)⟧'), eq₁₂', assoc, assoc, assoc, eq₁₃',
      iso₁₃.inv_hom_id_triangle_hom₃_assoc, ← rel₁₃]
  · rw [reassoc_of% eq₁₃, reassoc_of% rel₂₂, ← cancel_mono iso₂₃.hom.hom₃, assoc, assoc,
      iso₂₃.inv_hom_id_triangle_hom₃, eq₂₃]
    dsimp
    rw [comp_id]
  · rw [← cancel_mono (e₂.hom⟦(1 : ℤ)⟧'), assoc, assoc, assoc,assoc, eq₂₃',
      iso₂₃.inv_hom_id_triangle_hom₃_assoc, ← rel₂₃, ← Functor.map_comp, comm₁₂,
      Functor.map_comp, reassoc_of% eq₁₃']
  · refine isomorphic_distinguished _ H.mem _ ?_
    refine Triangle.isoMk _ _ (Triangle.π₃.mapIso iso₁₂) (Triangle.π₃.mapIso iso₁₃)
      (Triangle.π₃.mapIso iso₂₃) (by simp) (by simp) ?_
    dsimp
    rw [assoc, ← Functor.map_comp, eq₁₂, Functor.map_comp, reassoc_of% eq₂₃']

end Octahedron

end Triangulated

open Triangulated

/-- A triangulated category is a pretriangulated category which satisfies
the octahedron axiom (TR 4). -/
@[stacks 05QK]
class IsTriangulated : Prop where
  /-- the octahedron axiom (TR 4) -/
  octahedron_axiom :
    ∀ {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
      {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
      {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
      {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
      {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C),
      Nonempty (Octahedron comm h₁₂ h₂₃ h₁₃)

namespace Triangulated

variable {C}
variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C}
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C}
  (h : Octahedron comm h₁₂ h₂₃ h₁₃)

/-- A choice of octahedron given by the octahedron axiom. -/
def someOctahedron' [IsTriangulated C] : Octahedron comm h₁₂ h₂₃ h₁₃ :=
  (IsTriangulated.octahedron_axiom comm h₁₂ h₂₃ h₁₃).some

/-- A choice of octahedron given by the octahedron axiom. -/
def someOctahedron [IsTriangulated C]
    {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
    {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
    {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
    {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C) :
    Octahedron comm h₁₂ h₂₃ h₁₃ :=
  someOctahedron' _

end Triangulated

variable {C}

/-- Constructor for `IsTriangulated C` which shows that it suffices to obtain an octahedron
for a suitable isomorphic diagram instead of the given diagram. -/
lemma IsTriangulated.mk' (h : ∀ ⦃X₁' X₂' X₃' : C⦄ (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃'),
    ∃ (X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C) (u₁₂ : X₁ ⟶ X₂) (u₂₃ : X₂ ⟶ X₃) (e₁ : X₁' ≅ X₁) (e₂ : X₂' ≅ X₂)
    (e₃ : X₃' ≅ X₃) (_ : u₁₂' ≫ e₂.hom = e₁.hom ≫ u₁₂)
    (_ : u₂₃' ≫ e₃.hom = e₂.hom ≫ u₂₃)
    (v₁₂ : X₂ ⟶ Z₁₂) (w₁₂ : Z₁₂ ⟶ X₁⟦1⟧) (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
    (v₂₃ : X₃ ⟶ Z₂₃) (w₂₃ : Z₂₃ ⟶ X₂⟦1⟧) (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
    (v₁₃ : X₃ ⟶ Z₁₃) (w₁₃ : Z₁₃ ⟶ X₁⟦1⟧)
      (h₁₃ : Triangle.mk (u₁₂ ≫ u₂₃) v₁₃ w₁₃ ∈ distTriang C),
        Nonempty (Octahedron rfl h₁₂ h₂₃ h₁₃)) :
    IsTriangulated C where
  octahedron_axiom {X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' u₁₂' u₂₃' u₁₃'} comm'
    {v₁₂' w₁₂'} h₁₂' {v₂₃' w₂₃'} h₂₃' {v₁₃' w₁₃'} h₁₃' := by
    obtain ⟨X₁, X₂, X₃, Z₁₂, Z₂₃, Z₁₃, u₁₂, u₂₃, e₁, e₂, e₃, comm₁₂, comm₂₃,
      v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, H⟩ := h u₁₂' u₂₃'
    exact ⟨Octahedron.ofIso u₁₂' u₂₃' u₁₃' comm' h₁₂' h₂₃' h₁₃'
      u₁₂ u₂₃ _ rfl e₁ e₂ e₃ comm₁₂ comm₂₃ v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃ H.some⟩

end CategoryTheory
