/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Lemma
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Chosen finite products on sheaves

In this file, we put a `CartesianMonoidalCategory` instance on `A`-valued sheaves for a
`GrothendieckTopology` whenever `A` has a `CartesianMonoidalCategory` instance.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite Category Limits Sieve MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)
variable [CartesianMonoidalCategory A]

namespace Sheaf
variable (X Y : Sheaf J A)

lemma tensorProd_isSheaf : Presheaf.IsSheaf J (X.val ⊗ Y.val) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.val Y.val) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.val Y.val)

lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _

/-- Any `CartesianMonoidalCategory` on `A` induce a
`CartesianMonoidalCategory` structure on `A`-valued sheaves. -/
noncomputable instance cartesianMonoidalCategory : CartesianMonoidalCategory (Sheaf J A) :=
  .ofChosenFiniteProducts
    ({cone := asEmptyCone { val := 𝟙_ (Cᵒᵖ ⥤ A), cond := tensorUnit_isSheaf _}
      isLimit.lift f := ⟨toUnit f.pt.val⟩
      isLimit.fac := by rintro _ ⟨⟨⟩⟩
      isLimit.uniq x f h := Sheaf.hom_ext _ _ (toUnit_unique f.val _) })
  fun X Y ↦ {
    cone := BinaryFan.mk
        (P := { val := X.val ⊗ Y.val
                cond := tensorProd_isSheaf J X Y})
        ⟨(fst _ _)⟩ ⟨(snd _ _)⟩
    isLimit.lift f := ⟨lift (BinaryFan.fst f).val (BinaryFan.snd f).val⟩
    isLimit.fac := by rintro s ⟨⟨j⟩⟩ <;> apply Sheaf.hom_ext <;> simp
    isLimit.uniq x f h := by
      apply Sheaf.hom_ext
      apply CartesianMonoidalCategory.hom_ext
      · specialize h ⟨.left⟩
        rw [Sheaf.hom_ext_iff] at h
        simpa using h
      · specialize h ⟨.right⟩
        rw [Sheaf.hom_ext_iff] at h
        simpa using h
  }

@[simp] lemma cartesianMonoidalCategoryFst_val : (fst X Y).val = fst X.val Y.val := rfl
@[simp] lemma cartesianMonoidalCategorySnd_val : (snd X Y).val = snd X.val Y.val := rfl

variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)

@[simp] lemma cartesianMonoidalCategoryLift_val : (lift f g).val = lift f.val g.val := rfl
@[simp] lemma cartesianMonoidalCategoryWhiskerLeft_val : (X ◁ f).val = X.val ◁ f.val := rfl
@[simp] lemma cartesianMonoidalCategoryWhiskerRight_val : (f ▷ X).val = f.val ▷ X.val := rfl

end Sheaf

/-- The inclusion from sheaves to presheaves is monoidal with respect to the Cartesian monoidal
structures. -/
noncomputable instance sheafToPresheafMonoidal : (sheafToPresheaf J A).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := .refl _
      μIso F G := .refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] lemma sheafToPresheaf_ε : ε (sheafToPresheaf J A) = 𝟙 _ := rfl
@[simp] lemma sheafToPresheaf_η : η (sheafToPresheaf J A) = 𝟙 _ := rfl

variable {J}

@[simp] lemma sheafToPresheaf_μ (X Y : Sheaf J A) : μ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
@[simp] lemma sheafToPresheaf_δ (X Y : Sheaf J A) : δ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl

end CategoryTheory
