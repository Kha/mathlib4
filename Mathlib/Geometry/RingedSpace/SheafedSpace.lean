/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Functor Topology

universe u v w' w

variable (C : Type u) [Category.{v} C]


-- We could enable the following line:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opposite
-- but may need
-- https://github.com/leanprover-community/aesop/issues/59

namespace AlgebraicGeometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace extends PresheafedSpace C where
  /-- A sheafed space is a presheafed space which happens to be a sheaf. -/
  IsSheaf : presheaf.IsSheaf

variable {C}

namespace SheafedSpace

instance coeCarrier : CoeOut (SheafedSpace C) TopCat where coe X := X.carrier

instance coeSort : CoeSort (SheafedSpace C) Type* where
  coe X := X.1

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat) :=
  ⟨X.presheaf, X.IsSheaf⟩

/-- Not `@[simp]` since it already reduces to `carrier = carrier`. -/
theorem mk_coe (carrier) (presheaf) (h) :
    (({ carrier
        presheaf
        IsSheaf := h } : SheafedSpace C) : TopCat) = carrier :=
  rfl

instance (X : SheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

/-- The trivial `unit`-valued sheaf on any topological space. -/
def unit (X : TopCat) : SheafedSpace (Discrete Unit) :=
  { @PresheafedSpace.const (Discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }

instance : Inhabited (SheafedSpace (Discrete Unit)) :=
  ⟨unit (TopCat.of PEmpty)⟩

instance : Category (SheafedSpace C) :=
  show Category (InducedCategory (PresheafedSpace C) SheafedSpace.toPresheafedSpace) by
    infer_instance

@[ext (iff := false)]
theorem ext {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  PresheafedSpace.ext α β w h

/-- Constructor for isomorphisms in the category `SheafedSpace C`. -/
@[simps]
def isoMk {X Y : SheafedSpace C} (e : X.toPresheafedSpace ≅ Y.toPresheafedSpace) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
@[simps! obj map]
def forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance forgetToPresheafedSpace_full : (forgetToPresheafedSpace (C := C)).Full where
  map_surjective f := ⟨f, rfl⟩

instance forgetToPresheafedSpace_faithful : (forgetToPresheafedSpace (C := C)).Faithful where

instance is_presheafedSpace_iso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    @IsIso (PresheafedSpace C) _ _ _ f :=
  SheafedSpace.forgetToPresheafedSpace.map_isIso f

section

attribute [local simp] id comp

@[simp]
theorem id_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat) :=
  rfl

theorem id_c (X : SheafedSpace C) :
    (𝟙 X : X ⟶ X).c = eqToHom (Presheaf.Pushforward.id_eq X.presheaf).symm :=
  rfl

@[simp]
theorem id_c_app (X : SheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U = 𝟙 _ := rfl

@[simp]
theorem comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl

theorem comp_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app (op U) = β.c.app (op U) ≫ α.c.app (op ((Opens.map β.base).obj U)) :=
  rfl

theorem congr_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) :=
  PresheafedSpace.congr_app h U

variable (C)

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget : SheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map {_ _} f := f.base

end

open TopCat.Presheaf

/-- The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f) :
    SheafedSpace C :=
  { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_isOpenEmbedding h X.IsSheaf }

/-- The map from the restriction of a presheafed space.
-/
@[simps!]
def ofRestrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X := X.toPresheafedSpace.ofRestrict h

/-- The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
@[simps! hom inv]
def restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  isoMk (X.toPresheafedSpace.restrictTopIso)

/-- The global sections, notated Gamma.
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ

theorem Γ_def : (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl

@[simp]
theorem Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) :=
  rfl

theorem Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl

theorem Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

noncomputable instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    CreatesColimitsOfShape J (forgetToPresheafedSpace : SheafedSpace.{_, _, v} C ⥤ _) :=
  ⟨fun {K} =>
    createsColimitOfFullyFaithfulOfIso
      ⟨(PresheafedSpace.colimitCocone (K ⋙ forgetToPresheafedSpace)).pt,
        limit_isSheaf _ fun j ↦ Sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
      (colimit.isoColimitCocone ⟨_, PresheafedSpace.colimitCoconeIsColimit _⟩).symm⟩

noncomputable instance [HasLimits C] :
    CreatesColimits (forgetToPresheafedSpace : SheafedSpace C ⥤ _) where

instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J (SheafedSpace.{_, _, v} C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape forgetToPresheafedSpace

instance [HasLimits C] : HasColimits.{v} (SheafedSpace C) where

instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    PreservesColimitsOfShape J (forget.{_, _, v} C) :=
  Limits.comp_preservesColimitsOfShape forgetToPresheafedSpace (PresheafedSpace.forget C)

noncomputable instance [HasLimits C] : PreservesColimits (forget.{_, _, v} C) where

section ConcreteCategory

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [instCC : ConcreteCategory.{v} C FC] [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

attribute [local ext] DFunLike.ext in
include instCC in
lemma hom_stalk_ext {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.base = g.base)
    (h' : ∀ x, f.stalkMap x = (Y.presheaf.stalkCongr (h ▸ rfl)).hom ≫ g.stalkMap x) :
    f = g := by
  obtain ⟨f, fc⟩ := f
  obtain ⟨g, gc⟩ := g
  obtain rfl : f = g := h
  congr
  ext U s
  refine section_ext X.sheaf _ _ _ fun x hx ↦
    show X.presheaf.germ _ x _ _ = X.presheaf.germ _ x _ _ from ?_
  erw [← PresheafedSpace.stalkMap_germ_apply ⟨f, fc⟩, ← PresheafedSpace.stalkMap_germ_apply ⟨f, gc⟩]
  simp [h']

attribute [local ext] DFunLike.ext in
include instCC in
lemma mono_of_base_injective_of_stalk_epi {X Y : SheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Injective f.base)
    (h₂ : ∀ x, Epi (f.stalkMap x)) : Mono f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun x ↦ h₁ congr(($e).base x)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun x ↦ ?_
  rw [← cancel_epi (f.stalkMap (g x)), stalkCongr_hom, stalkSpecializes_refl, Category.id_comp,
    ← PresheafedSpace.stalkMap.comp ⟨g, gc⟩ f, ← PresheafedSpace.stalkMap.comp ⟨g, hc⟩ f]
  congr 1

attribute [local ext] DFunLike.ext in
include instCC in
lemma epi_of_base_surjective_of_stalk_mono {X Y : SheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.base)
    (h₂ : ∀ x, Mono (f.stalkMap x)) : Epi f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun y ↦ by
    rw [← (h₁ y).choose_spec]
    simpa using congr(($e).base.hom (h₁ y).choose)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun y ↦ ?_
  rw [← (h₁ y).choose_spec, ← cancel_mono (f.stalkMap (h₁ y).choose), stalkCongr_hom,
    stalkSpecializes_refl, Category.id_comp, ← PresheafedSpace.stalkMap.comp f ⟨g, gc⟩,
    ← PresheafedSpace.stalkMap.comp f ⟨g, hc⟩]
  congr 1

end ConcreteCategory

end SheafedSpace

end AlgebraicGeometry
