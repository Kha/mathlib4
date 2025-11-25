/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Fernando Chu, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.HasFibers
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# The Grothendieck construction gives a fibered category

In this file we show that the Grothendieck construction applied to a pseudofunctor `F`
gives a fibered category over the base category.

We also provide a `HasFibers` instance to `∫ᶜ F`, such that the fiber over `S` is the
category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

@[expose] public section

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Functor Opposite Bicategory Fiber

variable {𝒮 : Type*} [Category 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat}

section

variable {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S)

/-- The domain of the Cartesian lift of `f`. -/
abbrev domainCartesianLift : ∫ᶜ F := ⟨R, (F.map f.op.toLoc).obj a⟩

/-- The Cartesian lift of `f`. -/
abbrev cartesianLift : domainCartesianLift a f ⟶ ⟨S, a⟩ := ⟨f, 𝟙 _⟩

instance isHomLift_cartesianLift : IsHomLift (forget F) f (cartesianLift a f) :=
  IsHomLift.map (forget F) (cartesianLift a f)

variable {a} in
/-- Given some lift `φ'` of `g ≫ f`, the canonical map from the domain of `φ'` to the domain of
the Cartesian lift of `f`. -/
abbrev homCartesianLift {a' : ∫ᶜ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩)
    [IsHomLift (forget F) (g ≫ f) φ'] : a' ⟶ domainCartesianLift a f where
  base := g
  fiber :=
    have : φ'.base = g ≫ f := by simpa using IsHomLift.fac' (forget F) (g ≫ f) φ'
    φ'.fiber ≫ eqToHom (by simp [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.app a

instance isHomLift_homCartesianLift {a' : ∫ᶜ F} {φ' : a' ⟶ ⟨S, a⟩} {g : a'.1 ⟶ R}
    [IsHomLift (forget F) (g ≫ f) φ'] : IsHomLift (forget F) g (homCartesianLift f g φ') :=
  IsHomLift.map (forget F) (homCartesianLift f g φ')

lemma isStronglyCartesian_homCartesianLift :
    IsStronglyCartesian (forget F) f (cartesianLift a f) where
  universal_property' {a'} g φ' hφ' := by
    refine ⟨homCartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (g ≫ f) φ') (by simp)
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp

end

/-- `forget F : ∫ᶜ F ⥤ 𝒮` is a fibered category. -/
instance : IsFibered (forget F) :=
  IsFibered.of_exists_isStronglyCartesian (fun a _ f ↦
    ⟨domainCartesianLift a.2 f, cartesianLift a.2 f, isStronglyCartesian_homCartesianLift a.2 f⟩)

variable (F) (S : 𝒮)

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The inclusion map from `F(S)` into `∫ᶜ F`. -/
@[simps]
def ι : F.obj ⟨op S⟩ ⥤ ∫ᶜ F where
  obj a := { base := S, fiber := a}
  map {a b} φ := { base := 𝟙 S, fiber := φ ≫ (F.mapId ⟨op S⟩).inv.app b}
  map_comp {a b c} φ ψ := by
    ext
    · simp
    · simp [← (F.mapId ⟨op S⟩).inv.naturality_assoc ψ, F.whiskerRight_mapId_inv_app,
        Strict.leftUnitor_eqToIso]

/-- The natural isomorphism encoding `comp_const`. -/
@[simps!]
def compIso : (ι F S) ⋙ forget F ≅ (const (F.obj ⟨op S⟩)).obj S :=
  NatIso.ofComponents (fun a => eqToIso rfl)

lemma comp_const : (ι F S) ⋙ forget F = (const (F.obj ⟨op S⟩)).obj S :=
  Functor.ext_of_iso (compIso F S) (fun _ ↦ rfl) (fun _ => rfl)

noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).Full where
  map_surjective {X Y} f := by
    have hf : (fiberInclusion.map f).base = 𝟙 S := by
      simpa using (IsHomLift.fac (forget F) (𝟙 S) (fiberInclusion.map f)).symm
    use (fiberInclusion.map f).2 ≫ eqToHom (by simp [hf]) ≫ (F.mapId ⟨op S⟩).hom.app Y
    ext <;> simp [hf]

instance : (Fiber.inducedFunctor (comp_const F S)).Faithful where
  map_injective {a b} := by
    intro f g heq
    replace heq := fiberInclusion.congr_map heq
    simpa [cancel_mono] using ((Hom.ext_iff _ _).1 heq).2

noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).EssSurj := by
  apply essSurj_of_surj
  intro Y
  have hYS : (fiberInclusion.obj Y).base = S := by simpa using Y.2
  use hYS ▸ (fiberInclusion.obj Y).fiber
  apply fiberInclusion_obj_inj
  ext <;> simp [hYS]

noncomputable instance : (Fiber.inducedFunctor (comp_const F S)).IsEquivalence where

/-- `HasFibers` instance for `∫ᶜ F`, where the fiber over `S` is `F.obj ⟨op S⟩`. -/
noncomputable instance : HasFibers (forget F) where
  Fib S := F.obj ⟨op S⟩
  ι := ι F
  comp_const := comp_const F

end CategoryTheory.Pseudofunctor.CoGrothendieck
