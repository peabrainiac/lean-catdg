import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Category.TopCat.Basic

/-!
# The category `Mfld` of manifolds
In this file we define a general category `Mfld 𝕜 n` of all manifolds of a given smoothness degree
`n : WithTop ℕ∞` over a nontrivially normed ground field `𝕜`, imposing no conditions like
Hausdorffness, paracompactness, finite-dimensionality or boundarylessness. We instead set up
these properties as object properties, and define other categories of manifolds as full
subcategories in terms of them.

Currently this is all written with a focus on avoiding boilderplate code: we define each subcategory
as `P.FullSubcategory` for some object property `P`, and provide instances such as
`{P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ hausdorff)] (M : P.FullSubcategory) : T2Space M` to
avoid having to set up `T2Space`-instances for each considere subcategory separately. The downsides
of this approach are that dot notation doesn't carry over to full subcategories, and that we
have to define some instances like `[Fact (a ≤ c)] : Fact (a ⊓ b ≤ c)`.

## Main definitions / results
* `Mfld 𝕜 n`: the category of all Cⁿ manifolds with corners over a fixed ground field `𝕜`.
* `FinDimMfld 𝕜 n`: the category of Hausdorff, paracompact finite-dimensional manifolds without
  boundary, defined as a full subcategory of `Mfld 𝕜 n`.
* `FinDimMfldWCorners 𝕜 n`: the category of Hausdorff, paracompact finite-dimensional manifolds
  with corners, defined as a full subcategory of `Mfld 𝕜 n`.
* `BanachMfld 𝕜 n`: the category of Hausdorff, paracompact Banach manifolds without boundary,
  defined as a full subcategory of `Mfld 𝕜 n`.
* All of these subcategories are concrete.

For each of these subcategories a forgetful functor to `TopCat`, an inclusion into `Mfld 𝕜 n` and
inclusions into other subcategories are provided in the form of `HasForget₂`-instances.

## TODOs
* Show that `Mfld 𝕜 n` has all products.
* Show that various object properties are closed under arbitrary / finite products, and conclude
  that the subcategories under consideration also have arbitrary / finite products.
-/

universe u

open CategoryTheory

/-- The category of all (possbily non-Hausdorff, non-paracompact and infinite-dimensional) manifolds
with corners for a fixed ground field `𝕜` and smoothness degree `n : WithTop ℕ∞`.
The main purpose of this category is to act as an ambient category for nicer categories of manifolds
to be considered as full subcategories of. -/
structure Mfld (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  {modelVectorSpace : Type u}
  [normedAddCommGroup : NormedAddCommGroup modelVectorSpace]
  [normedSpace : NormedSpace 𝕜 modelVectorSpace]
  {model : Type u}
  [modelTopology : TopologicalSpace model]
  modelWithCorners : ModelWithCorners 𝕜 modelVectorSpace model
  [chartedSpace : ChartedSpace model carrier]
  [isManifold : IsManifold modelWithCorners n carrier]

attribute [instance] Mfld.topology Mfld.normedAddCommGroup Mfld.normedSpace
  Mfld.modelTopology Mfld.chartedSpace Mfld.isManifold

namespace Mfld

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}

instance : CoeSort (Mfld 𝕜 n) (Type u) :=
  ⟨Mfld.carrier⟩

instance (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) : Category (Mfld 𝕜 n) where
  Hom M N := ContMDiffMap M.modelWithCorners N.modelWithCorners M.carrier N.carrier n
  id M := ContMDiffMap.id
  comp f g := g.comp f

instance : ConcreteCategory.{u} (Mfld 𝕜 n)
    (fun M N => ContMDiffMap M.modelWithCorners N.modelWithCorners M N n) where
  hom f := f
  ofHom f := f

@[simps]
instance : HasForget₂ (Mfld 𝕜 n) TopCat where
  forget₂ := { obj M := .of M, map (f : ContMDiffMap _ _ _ _ _) := TopCat.ofHom f }

/-- The object property satisfied by all manifolds whose underlying topological space is T2. -/
def hausdorff : ObjectProperty (Mfld 𝕜 n) :=
  fun M ↦ T2Space M

/-- The object property satisfied by all σ-compact manifolds. -/
def sigmaCompact : ObjectProperty (Mfld 𝕜 n) :=
  fun M ↦ SigmaCompactSpace M

/-- The object property satisfied by all manifolds that are boundaryless in the sense of
`BoundarylessManifold`. Note that such manifolds can still be modelled on non-boundaryless
models with corners, they just need to consist entirely of interior points. -/
def boundaryless : ObjectProperty (Mfld 𝕜 n) :=
  fun M ↦ BoundarylessManifold M.modelWithCorners M

/-- The object property satisfied by all manifolds whose model vector space is complete. -/
def banach : ObjectProperty (Mfld 𝕜 n) :=
  fun M ↦ CompleteSpace M.modelVectorSpace

/-- The object property satisfied by all manifolds whose model vector space is
finite-dimensional. -/
def finiteDimensional : ObjectProperty (Mfld 𝕜 n) :=
  fun M ↦ FiniteDimensional 𝕜 M.modelVectorSpace

lemma finiteDimensional_le_banach [CompleteSpace 𝕜] :
    finiteDimensional (𝕜 := 𝕜) (n := n) ≤ banach :=
  fun _ (_ : FiniteDimensional 𝕜 _) ↦ FiniteDimensional.complete 𝕜 _

/-- The object property corresponding to Hausdorff, sigma-compact and finite-dimensional manifolds
without boundary. -/
abbrev finDimMfld : ObjectProperty (Mfld 𝕜 n) :=
  hausdorff ⊓ sigmaCompact ⊓ boundaryless ⊓ finiteDimensional

/-- The object property corresponding to Hausdorff, sigma-compact and finite-dimensional manifolds
with corners. -/
abbrev finDimMfldWCorners : ObjectProperty (Mfld 𝕜 n) :=
  hausdorff ⊓ sigmaCompact ⊓ finiteDimensional

/-- The object property corresponding to Hausdorff sigma-compact Banach manifolds
without boundary. -/
abbrev banachMfld : ObjectProperty (Mfld 𝕜 n) :=
  hausdorff ⊓ sigmaCompact ⊓ boundaryless ⊓ banach

lemma finDimMfld_le_finDimMfldWCorners : finDimMfld (𝕜 := 𝕜) (n := n) ≤ finDimMfldWCorners :=
  inf_le_inf_right _ <| inf_le_left

lemma finDimMfld_le_banachMfld [CompleteSpace 𝕜] : finDimMfld (𝕜 := 𝕜) (n := n) ≤ banachMfld :=
  inf_le_inf_left _ finiteDimensional_le_banach

/-- The category of (Hausdorff, paracompact) finite-dimensional manifolds without boundary,
defined as a full subcategory of `Mfld 𝕜 n`. -/
abbrev _root_.FinDimMfld (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) :=
  finDimMfld.FullSubcategory (C := Mfld.{u} 𝕜 n)

/-- The category of (Hausdorff, paracompact) finite-dimensional manifolds with corners,
defined as a full subcategory of `Mfld 𝕜 n`. -/
abbrev _root_.FinDimMfldWCorners (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) :=
  finDimMfldWCorners.FullSubcategory (C := Mfld.{u} 𝕜 n)

/-- The category of (Hausdorff, paracompact) Banach manifolds without boundary,
defined as a full subcategory of `Mfld 𝕜 n`. -/
abbrev _root_.BanachMfld (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) :=
  banachMfld.FullSubcategory (C := Mfld.{u} 𝕜 n)

/-- Each subcategory defined in this way automatically carries the structure of a concrete category
and a forgetful functor to `(Mfld 𝕜 n)`. -/
example : HasForget₂ (FinDimMfld 𝕜 n) (Mfld 𝕜 n) := inferInstance

-- TODO: move this somewhere else
instance {C : Type*} [Category C] [CoeSort C (Type u)] (P : ObjectProperty C) :
    CoeSort P.FullSubcategory (Type u) :=
  ⟨fun X ↦ X.obj⟩

example : CoeSort (FinDimMfld 𝕜 n) (Type u) := inferInstance

-- TODO: move this somewhere else
instance {α : Type u} [SemilatticeInf α] {a : α} : Fact (a ≤ a) := ⟨le_refl a⟩

-- TODO: move this somewhere else
instance {α : Type u} [SemilatticeInf α] {a b c : α} [Fact (a ≤ c)] : Fact (a ⊓ b ≤ c) :=
  ⟨inf_le_of_left_le Fact.out⟩

-- TODO: move this somewhere else
instance {α : Type u} [SemilatticeInf α] {a b c : α} [Fact (b ≤ c)] : Fact (a ⊓ b ≤ c) :=
  ⟨inf_le_of_right_le Fact.out⟩

instance {P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ hausdorff)] (M : P.FullSubcategory) :
    T2Space M :=
  (Fact.out : P ≤ hausdorff) _ M.property

instance {P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ sigmaCompact)] (M : P.FullSubcategory) :
    SigmaCompactSpace M :=
  (Fact.out : P ≤ sigmaCompact) _ M.property

instance {P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ boundaryless)] (M : P.FullSubcategory) :
    BoundarylessManifold M.obj.modelWithCorners M :=
  (Fact.out : P ≤ boundaryless) _ M.property

instance {P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ banach)] (M : P.FullSubcategory) :
    CompleteSpace M.obj.modelVectorSpace :=
  (Fact.out : P ≤ banach) _ M.property

instance {P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ finiteDimensional)] (M : P.FullSubcategory) :
    FiniteDimensional 𝕜 M.obj.modelVectorSpace :=
  (Fact.out : P ≤ finiteDimensional) _ M.property

/-- Every object of one of these subcategories automatically receives all the correct instances. -/
example (M : FinDimMfld 𝕜 n) : T2Space M := inferInstance

-- TODO: move this somewhere else
@[simps]
instance {C D : Type*} [Category C] [Category D] [HasForget.{u} C] [HasForget.{u} D]
    [HasForget₂ C D] (P : ObjectProperty C) : HasForget₂ P.FullSubcategory D :=
  ⟨forget₂ _ C ⋙ forget₂ C D, by simp [Functor.assoc, HasForget₂.forget_comp]⟩

/-- Each of these subcategories automatically also carries a forgetful functor to `TopCat`. -/
example : HasForget₂ (FinDimMfld 𝕜 n) TopCat := inferInstance

-- TODO: move this somewhere else, get `@[simps]` to work
instance {C : Type*} [Category C] [HasForget.{u} C] (P : ObjectProperty C) (Q : ObjectProperty C)
    [Fact (P ≤ Q)] : HasForget₂ P.FullSubcategory Q.FullSubcategory :=
  ⟨P.ιOfLE Fact.out, rfl⟩

instance : Fact (finDimMfld (𝕜 := 𝕜) (n := n) ≤ finDimMfldWCorners) :=
  ⟨finDimMfld_le_finDimMfldWCorners⟩

instance [CompleteSpace 𝕜] : Fact (finDimMfld ≤ banachMfld (𝕜 := 𝕜) (n := n)) :=
  ⟨finDimMfld_le_banachMfld⟩

/-- We have also have forgetful functors between the different subcategories. -/
example : HasForget₂ (FinDimMfld 𝕜 n) (FinDimMfldWCorners 𝕜 n) := inferInstance

example [CompleteSpace 𝕜] : HasForget₂ (FinDimMfld 𝕜 n) (BanachMfld 𝕜 n) := inferInstance

end Mfld
