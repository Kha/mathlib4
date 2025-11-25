/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Tactic.TypeStar

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D `from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $$ Hom_C(X, Y) = Hom_D(FX, FY) $$. We call this the
category induced from `D` along `F`.

## Implementation notes

It looks odd to make `D` an explicit argument of `InducedCategory`,
when it is determined by the argument `F` anyways. The reason to make `D`
explicit is in order to control its syntactic form, so that instances
like `InducedCategory.has_forget₂` (elsewhere) refer to the correct
form of `D`. This is used to set up several algebraic categories like

  def CommMon : Type (u+1) := InducedCategory Mon (Bundled.map @CommMonoid.toMonoid)
  -- not `InducedCategory (Bundled Monoid) (Bundled.map @CommMonoid.toMonoid)`,
  -- even though `MonCat = Bundled Monoid`!
-/

@[expose] public section


namespace CategoryTheory

universe v v₂ u₁ u₂
-- morphism levels before object levels. See note [category theory universes].

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]
variable (F : C → D)

/-- `InducedCategory D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint unusedArguments]
def InducedCategory (_F : C → D) : Type u₁ :=
  C

variable {D}

instance InducedCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedCategory D F) α :=
  ⟨fun c => F c⟩

instance InducedCategory.category : Category.{v} (InducedCategory D F) where
  Hom X Y := F X ⟶ F Y
  id X := 𝟙 (F X)
  comp f g := f ≫ g

variable {F} in
/-- Construct an isomorphism in the induced category
from an isomorphism in the original category. -/
@[simps] def InducedCategory.isoMk {X Y : InducedCategory D F} (f : F X ≅ F Y) : X ≅ Y where
  hom := f.hom
  inv := f.inv
  hom_inv_id := f.hom_inv_id
  inv_hom_id := f.inv_hom_id

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map f := f

/-- The induced functor `inducedFunctor F : InducedCategory D F ⥤ D` is fully faithful. -/
def fullyFaithfulInducedFunctor : (inducedFunctor F).FullyFaithful where
  preimage f := f

instance InducedCategory.full : (inducedFunctor F).Full :=
  (fullyFaithfulInducedFunctor F).full

instance InducedCategory.faithful : (inducedFunctor F).Faithful :=
  (fullyFaithfulInducedFunctor F).faithful

end Induced

end CategoryTheory
