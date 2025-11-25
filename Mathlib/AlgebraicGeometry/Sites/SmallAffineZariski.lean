/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.Tactic.Lemma

/-!

# The small affine Zariski site

`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`.

Every presieve on `U` is then given by a `Set Γ(X, U)` (`presieveOfSections_surjective`), and
we endow `X.AffineZariskiSite` with `grothendieckTopology X`, such that `s : Set Γ(X, U)` is
a cover if and only if `Ideal.span s = ⊤` (`generate_presieveOfSections_mem_grothendieckTopology`).

This is a dense subsite of `X.Opens` (with respect to `Opens.grothendieckTopology X`) via the
inclusion functor `toOpensFunctor X`,
which gives an equivalence of categories of sheaves (`sheafEquiv`).

Note that this differs from the definition on stacks project where the arrows in the small affine
Zariski site are arbitrary inclusions.

-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/--
`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`.

Note that this differs from the definition on stacks project where the arrows in the small affine
Zariski site are arbitrary inclusions.
-/
def Scheme.AffineZariskiSite (X : Scheme.{u}) : Type u := { U : X.Opens // IsAffineOpen U }

namespace Scheme.AffineZariskiSite

/-- The inclusion from `X.AffineZariskiSite` to `X.Opens`. -/
abbrev toOpens (U : X.AffineZariskiSite) : X.Opens := U.1

instance : Preorder X.AffineZariskiSite where
  le U V := ∃ f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens
  le_refl U := ⟨1, Scheme.basicOpen_of_isUnit _ isUnit_one⟩
  le_trans := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact hW.basicOpen_basicOpen_is_basicOpen g f

lemma toOpens_mono :
    Monotone (toOpens (X := X)) := by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨f, rfl⟩
  exact X.basicOpen_le _

lemma toOpens_injective : Function.Injective (toOpens (X := X)) := Subtype.val_injective

instance : PartialOrder X.AffineZariskiSite where
  le_antisymm _ _ hUV hVU := Subtype.ext ((toOpens_mono hUV).antisymm (toOpens_mono hVU))

/-- The basic open set of a section, as an element of `AffineZariskiSite`. -/
def basicOpen (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : X.AffineZariskiSite :=
  ⟨X.basicOpen f, U.2.basicOpen f⟩

lemma basicOpen_le (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f ≤ U :=
  ⟨f, rfl⟩

variable (X) in
/-- The inclusion functor from `X.AffineZariskiSite` to `X.Opens`. -/
def toOpensFunctor : X.AffineZariskiSite ⥤ X.Opens := toOpens_mono.functor

instance : (toOpensFunctor X).Faithful where

instance : (toOpensFunctor X).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V h x hx
    obtain ⟨f, hfU, hxf⟩ := V.2.exists_basicOpen_le ⟨x, hx⟩ (h.le hx)
    exact ⟨X.basicOpen f, homOfLE hfU, ⟨V.basicOpen f,
      ⟨_, (X.basicOpen_res f h.op).trans (inf_eq_right.mpr hfU)⟩, 𝟙 _,
      ⟨⟨f, rfl⟩, rfl⟩, rfl⟩, hxf⟩

instance : (toOpensFunctor X).IsCoverDense (Opens.grothendieckTopology X) where
  is_cover := by
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, 𝟙 _, homOfLE hVU, rfl⟩, hxV⟩

variable (X) in
/-- The Grothendieck topology on `X.AffineZariskiSite` induced from the topology on `X.Opens`.
Also see `mem_grothendieckTopology_iff_sectionsOfPresieve`. -/
def grothendieckTopology : GrothendieckTopology X.AffineZariskiSite :=
  (toOpensFunctor X).inducedTopology (Opens.grothendieckTopology X)

lemma mem_grothendieckTopology {U : X.AffineZariskiSite} {S : Sieve U} :
    S ∈ grothendieckTopology X U ↔
      ∀ x ∈ U.toOpens, ∃ (V : _) (f : V ⟶ U), S.arrows f ∧ x ∈ V.toOpens := by
  apply forall₂_congr fun x hxU ↦ ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨W, g, h, hg, rfl⟩, hxV⟩
    exact ⟨W, g, hg, h.le hxV⟩
  · rintro ⟨W, g, hg, hxW⟩
    exact ⟨W.toOpens, homOfLE (toOpens_mono g.le), ⟨W, g, 𝟙 _, hg, rfl⟩, hxW⟩

instance : (toOpensFunctor X).IsDenseSubsite
    (grothendieckTopology X) (Opens.grothendieckTopology X) where
  functorPushforward_mem_iff := Iff.rfl

/-- The presieve associated to a set of sections.
This is a surjection, see `presieveOfSections_surjective`. -/
def presieveOfSections (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) : Presieve U :=
  fun V _ ↦ ∃ f ∈ s, X.basicOpen f = V.toOpens

/-- The set of sections associated to a presieve. -/
def sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) : Set Γ(X, U.toOpens) :=
  { f | P (homOfLE (U.basicOpen_le f)) }

lemma presieveOfSections_sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) :
    presieveOfSections U (sectionsOfPresieve P) = P := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ ↦ eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨_, H, rfl⟩
    exact H
  · intro H
    obtain rfl : _ = V := hf
    exact ⟨_, H, rfl⟩

lemma presieveOfSections_surjective {U : X.AffineZariskiSite} :
    Function.Surjective (presieveOfSections U) :=
  fun _ ↦ ⟨_, presieveOfSections_sectionsOfPresieve _⟩

lemma presieveOfSections_eq_ofArrows (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) :
    presieveOfSections U s = .ofArrows _ (fun i : s ↦ homOfLE (U.basicOpen_le i.1)) := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ ↦ eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨f, hfs, rfl⟩
    exact .mk (ι := s) ⟨f, hfs⟩
  · rintro ⟨⟨f, hfs⟩⟩
    exact ⟨f, hfs, rfl⟩

lemma generate_presieveOfSections
    {U V : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} {f : V ⟶ U} :
    Sieve.generate (presieveOfSections U s) f ↔ ∃ f ∈ s, ∃ g, X.basicOpen (f * g) = V.toOpens := by
  obtain ⟨V, hV⟩ := V
  constructor
  · rintro ⟨⟨W, hW⟩, ⟨f₁, hf₁⟩, -, ⟨f₂, hf₂s, rfl⟩, rfl⟩
    subst hf₁
    obtain ⟨f₃, hf₃⟩ := U.2.basicOpen_basicOpen_is_basicOpen f₂ f₁
    refine ⟨f₂, hf₂s, f₃, ?_⟩
    rw [X.basicOpen_mul, hf₃, inf_eq_right]
    exact X.basicOpen_le _
  · rintro ⟨f₁, hf₁s, f₂, rfl⟩
    refine ⟨U.basicOpen f₁, ⟨f₂ |_ _, ?_⟩, ⟨f₁, rfl⟩, ⟨f₁, hf₁s, rfl⟩, rfl⟩
    exact (X.basicOpen_res _ _).trans (X.basicOpen_mul _ _).symm

lemma generate_presieveOfSections_mem_grothendieckTopology
    {U : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} :
    Sieve.generate (presieveOfSections U s) ∈ grothendieckTopology X U ↔ Ideal.span s = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff, mem_grothendieckTopology, SetLike.le_def]
  refine forall₂_congr fun x hx ↦ ?_
  simp only [exists_and_left, TopologicalSpace.Opens.iSup_mk,
    TopologicalSpace.Opens.carrier_eq_coe, Set.iUnion_coe_set, TopologicalSpace.Opens.mem_mk,
    Set.mem_iUnion, SetLike.mem_coe, exists_prop, generate_presieveOfSections]
  constructor
  · simp only [basicOpen_mul]
    rintro ⟨⟨V, hV⟩, ⟨f, hfs, g, rfl⟩, -, hxV⟩
    exact ⟨f, hfs, hxV.1⟩
  · rintro ⟨f, hfs, hxf⟩
    refine ⟨U.basicOpen _, ⟨f, hfs, 1, rfl⟩, ⟨_, rfl⟩, by simpa using hxf⟩

lemma mem_grothendieckTopology_iff_sectionsOfPresieve
    {U : X.AffineZariskiSite} {S : Sieve U} :
    S ∈ grothendieckTopology X U ↔ Ideal.span (sectionsOfPresieve S.1) = ⊤ := by
  rw [← generate_presieveOfSections_mem_grothendieckTopology, presieveOfSections_sectionsOfPresieve,
    Sieve.generate_sieve]

variable {A} [Category A]
variable [∀ (U : X.Opensᵒᵖ), Limits.HasLimitsOfShape (StructuredArrow U (toOpensFunctor X).op) A]

/-- The category of sheaves on `X.AffineZariskiSite` is equivalent to the categories of sheaves
over `X`. -/
abbrev sheafEquiv : Sheaf (grothendieckTopology X) A ≌ TopCat.Sheaf A X :=
    (toOpensFunctor X).sheafInducedTopologyEquivOfIsCoverDense _ _

end Scheme.AffineZariskiSite

end AlgebraicGeometry
