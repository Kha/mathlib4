/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subpresheaf.Image

/-!
# The equalizer of two morphisms of presheaves, as a subpresheaf

If `F₁` and `F₂` are presheaves of types, `A : Subpresheaf F₁`, and
`f` and `g` are two morphisms `A.toPresheaf ⟶ F₂`, we introduce
`Subcomplex.equalizer f g`, which is the subpresheaf of `F₁` contained in `A`
where `f` and `g` coincide.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F₁ F₂ : Cᵒᵖ ⥤ Type w} {A : Subpresheaf F₁}
  (f g : A.toPresheaf ⟶ F₂)

namespace Subpresheaf

/-- The equalizer of two morphisms of presheaves of types of the form
`A.toPresheaf ⟶ F₂` with `A : Subpresheaf F₁`, as a subcomplex of `F₁`. -/
@[simps -isSimp]
protected def equalizer : Subpresheaf F₁ where
  obj U := setOf (fun x ↦ ∃ (hx : x ∈ A.obj _), f.app _ ⟨x, hx⟩ = g.app _ ⟨x, hx⟩)
  map φ x := by
    rintro ⟨hx, h⟩
    exact ⟨A.map _ hx,
      (FunctorToTypes.naturality _ _ f φ ⟨x, hx⟩).trans (Eq.trans (by rw [h])
        (FunctorToTypes.naturality _ _ g φ ⟨x, hx⟩).symm)⟩

attribute [local simp] equalizer_obj

lemma equalizer_le : Subpresheaf.equalizer f g ≤ A :=
  fun _ _ h ↦ h.1

@[simp]
lemma equalizer_self : Subpresheaf.equalizer f f = A := by aesop

lemma mem_equalizer_iff {i : Cᵒᵖ} (x : A.toPresheaf.obj i) :
    x.1 ∈ (Subpresheaf.equalizer f g).obj i ↔ f.app i x = g.app i x := by
  simp

lemma range_le_equalizer_iff {G : Cᵒᵖ ⥤ Type w} (φ : G ⟶ A.toPresheaf) :
    range (φ ≫ A.ι) ≤ Subpresheaf.equalizer f g ↔ φ ≫ f = φ ≫ g := by
  rw [NatTrans.ext_iff]
  simp [le_def, Set.subset_def, funext_iff, CategoryTheory.types_ext_iff]

lemma equalizer_eq_iff :
    Subpresheaf.equalizer f g = A ↔ f = g := by
  have := range_le_equalizer_iff f g (𝟙 _)
  simp only [Category.id_comp, range_ι] at this
  rw [← this]
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm (equalizer_le f g) h

/-- Given two morphisms `f` and `g` in `A.toPresheaf ⟶ F₂`, this is the monomorphism
of presheaves corresponding to the inclusion `Subpresheaf.equalizer f g ≤ A`. -/
def equalizer.ι : (Subpresheaf.equalizer f g).toPresheaf ⟶ A.toPresheaf :=
  homOfLe (equalizer_le f g)

instance : Mono (equalizer.ι f g) := by
  dsimp [equalizer.ι]
  infer_instance

@[reassoc (attr := simp)]
lemma equalizer.ι_ι : equalizer.ι f g ≫ A.ι = (Subpresheaf.equalizer f g).ι := rfl

@[reassoc]
lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g := by
  simp [← range_le_equalizer_iff]

/-- Given two morphisms `f` and `g` in `A.toPresheaf ⟶ F₂`, if `φ : G ⟶ A.toPresheaf`
is such that `φ ≫ f = φ ≫ g`, then this is the lifted morphism
`G ⟶ (Subpresheaf.equalizer f g).toPresheaf`. This is part of the universal
property of the equalizer that is satisfied by
the presheaf `(Subpresheaf.equalizer f g).toPresheaf`. -/
def equalizer.lift {G : Cᵒᵖ ⥤ Type w} (φ : G ⟶ A.toPresheaf)
    (w : φ ≫ f = φ ≫ g) :
    G ⟶ (Subpresheaf.equalizer f g).toPresheaf :=
  Subpresheaf.lift (φ ≫ A.ι) (by simpa only [range_le_equalizer_iff] using w)

@[reassoc (attr := simp)]
lemma equalizer.lift_ι' {G : Cᵒᵖ ⥤ Type w} (φ : G ⟶ A.toPresheaf)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ (Subpresheaf.equalizer f g).ι = φ ≫ A.ι :=
  rfl

@[reassoc (attr := simp)]
lemma equalizer.lift_ι {G : Cᵒᵖ ⥤ Type w} (φ : G ⟶ A.toPresheaf)
    (w : φ ≫ f = φ ≫ g) :
    equalizer.lift f g φ w ≫ equalizer.ι f g = φ :=
  rfl

/-- The (limit) fork which expresses `(Subpresheaf.equalizer f g).toPresheaf` as
the equalizer of `f` and `g`. -/
@[simps! pt]
def equalizer.fork : Limits.Fork f g :=
  Limits.Fork.ofι (equalizer.ι f g) (equalizer.condition f g)

@[simp]
lemma equalizer.fork_ι :
    (equalizer.fork f g).ι = equalizer.ι f g := rfl

/-- `(Subpresheaf.equalizer f g).toPresheaf` is the equalizer of `f` and `g`. -/
def equalizer.forkIsLimit : Limits.IsLimit (equalizer.fork f g) :=
  Limits.Fork.IsLimit.mk _
    (fun s ↦ equalizer.lift _ _ s.ι s.condition)
    (fun s ↦ by dsimp)
    (fun s m hm ↦ by simp [← cancel_mono (Subpresheaf.equalizer f g).ι, ← hm])

end Subpresheaf

end CategoryTheory
