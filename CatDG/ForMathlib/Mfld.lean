import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.Geometry.Manifold.LocalDiffeomorph
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

We also show that isomorphisms in the category of manifolds are diffeomorphisms and that
some of the introduced object properties are invariant under isomorphism. Unfortunately,
all properties pertaining to the model spaces of the manifolds are not invariant under isomorphism,
because the empty type is a manifold for all model spaces simultaneously. One could try to
work around this in the future by defining e.g. `banach M` as
`IsEmpty M ∨ CompleteSpace M.modelVectorSpace` instead of just `CompleteSpace M.modelVectorSpace`;
that way `banach` would be closed under isomorphisms, but instances like
`CompleteSpace M.obj.modelVectorSpace` for `M : BanachMfld 𝕜 n` could only be provided under
the assumption `Nonempty M`.

Lastly, we give a construction of finite products in `Mfld 𝕜 n`.

## TODOs
* Show that `boundaryless` is closed under isomorphisms.
* Redefine `banach` and `finiteDimensional` such that they are closed under isomorphisms too.
* Show that various object properties are closed under finite products, and conclude
  that the subcategories under consideration also have finite products. This requires
  showing that they are closed under isomorphisms first, because
  `ObjectProperty.IsClosedUnderLimitsOfShape` is defined to mean that the property contains not just
  some but all limits of diagrams within it.
* Make use of `Mathlib.CategoryTheory.ObjectProperty.FiniteProducts` here once mathlib is bumped
  again.
-/

universe u

open CategoryTheory ConcreteCategory Limits Manifold

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
  fun M ↦ IsEmpty M ∨ CompleteSpace M.modelVectorSpace

/-- The object property satisfied by all manifolds whose model vector space is
finite-dimensional. -/
def finiteDimensional : ObjectProperty (Mfld 𝕜 n) :=
  fun M ↦ IsEmpty M ∨ FiniteDimensional 𝕜 M.modelVectorSpace

lemma finiteDimensional_le_banach [CompleteSpace 𝕜] :
    finiteDimensional (𝕜 := 𝕜) (n := n) ≤ banach :=
  fun _ ↦ Or.imp_right fun h ↦ h.complete 𝕜 _

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

instance {P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ banach)] (M : P.FullSubcategory) [Nonempty M] :
    CompleteSpace M.obj.modelVectorSpace :=
  (or_iff_right <| not_isEmpty_of_nonempty _).1 <| (Fact.out : P ≤ banach) _ M.property

instance {P : ObjectProperty (Mfld 𝕜 n)} [Fact (P ≤ finiteDimensional)] (M : P.FullSubcategory)
    [Nonempty M] :
    FiniteDimensional 𝕜 M.obj.modelVectorSpace :=
  (or_iff_right <| not_isEmpty_of_nonempty _).1 <| (Fact.out : P ≤ finiteDimensional) _ M.property

/-- Every object of one of these subcategories automatically receives all the correct instances. -/
example (M : FinDimMfld 𝕜 n) : T2Space M := inferInstance

-- TODO: move this somewhere else
@[simps]
instance {C D : Type*} [Category C] {FC : C → C → Type u} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [Category D] {FD : D → D → Type u} {CD : D → Type u}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [HasForget₂ C D] (P : ObjectProperty C) : HasForget₂ P.FullSubcategory D :=
  ⟨forget₂ _ C ⋙ forget₂ C D, by simp [Functor.assoc, HasForget₂.forget_comp]⟩

/-- Each of these subcategories automatically also carries a forgetful functor to `TopCat`. -/
example : HasForget₂ (FinDimMfld 𝕜 n) TopCat := inferInstance

-- TODO: move this somewhere else, get `@[simps]` to work
instance {C : Type*} [Category C] {FC : C → C → Type u} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    (P : ObjectProperty C) (Q : ObjectProperty C) [Fact (P ≤ Q)] :
    HasForget₂ P.FullSubcategory Q.FullSubcategory :=
  ⟨P.ιOfLE Fact.out, rfl⟩

instance : Fact (finDimMfld (𝕜 := 𝕜) (n := n) ≤ finDimMfldWCorners) :=
  ⟨finDimMfld_le_finDimMfldWCorners⟩

instance [CompleteSpace 𝕜] : Fact (finDimMfld ≤ banachMfld (𝕜 := 𝕜) (n := n)) :=
  ⟨finDimMfld_le_banachMfld⟩

/-- We have also have forgetful functors between the different subcategories. -/
example : HasForget₂ (FinDimMfld 𝕜 n) (FinDimMfldWCorners 𝕜 n) := inferInstance

example [CompleteSpace 𝕜] : HasForget₂ (FinDimMfld 𝕜 n) (BanachMfld 𝕜 n) := inferInstance

section Isomorphisms

@[simps]
def isoOfDiffeomorph {M N : Mfld 𝕜 n} (d : M ≃ₘ^n⟮M.modelWithCorners,N.modelWithCorners⟯ N) :
    M ≅ N where
  hom := ofHom d.toContMDiffMap
  inv := ofHom d.symm.toContMDiffMap
  hom_inv_id := by ext x; simp [hom_ofHom]
  inv_hom_id := by ext x; simp [hom_ofHom]

@[simps]
def diffeomorphOfIso {M N : Mfld 𝕜 n} (i : M ≅ N) :
    M ≃ₘ^n⟮M.modelWithCorners,N.modelWithCorners⟯ N where
  toFun := hom i.hom
  invFun := hom i.inv
  contMDiff_toFun := (hom i.hom).2
  contMDiff_invFun := (hom i.inv).2
  left_inv x := by simp
  right_inv x := by simp

@[simp]
lemma isoOfDiffeomorph_diffeomorphOfIso {M N : Mfld 𝕜 n} (i : M ≅ N) :
    isoOfDiffeomorph (diffeomorphOfIso i) = i := by rfl

@[simp]
lemma diffeomorphOfIso_isoOfDiffeomorph {M N : Mfld 𝕜 n}
    (d : M ≃ₘ^n⟮M.modelWithCorners,N.modelWithCorners⟯ N) :
    diffeomorphOfIso (isoOfDiffeomorph d) = d := by rfl

@[simps]
def isoEquivDiffeomorph {M N : Mfld 𝕜 n} :
    (M ≅ N) ≃ (M ≃ₘ^n⟮M.modelWithCorners,N.modelWithCorners⟯ N) where
  toFun := diffeomorphOfIso
  invFun := isoOfDiffeomorph

end Isomorphisms

section ClosedUnderIsomorphisms

instance : hausdorff.IsClosedUnderIsomorphisms (C := Mfld.{u} 𝕜 n) :=
  ⟨fun i (_ : T2Space _) ↦ (diffeomorphOfIso i).toHomeomorph.t2Space⟩

-- TODO: move this somewhere else
lemma _root_.Homeomorph.sigmaCompactSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [SigmaCompactSpace X] (h : X ≃ₜ Y) : SigmaCompactSpace Y := by
  rwa [← isSigmaCompact_univ_iff, ← h.isSigmaCompact_preimage, Set.preimage_univ,
    isSigmaCompact_univ_iff]

instance : sigmaCompact.IsClosedUnderIsomorphisms (C := Mfld.{u} 𝕜 n) :=
  ⟨fun i (_ : SigmaCompactSpace _) ↦ (diffeomorphOfIso i).toHomeomorph.sigmaCompactSpace⟩

/-- TODO: prove this. This involves showing that the boundary and interior of manifolds
are preserved by diffeomorphisms, which probably needs #33189 to be merged first. -/
proof_wanted instIsClosedUnderIsomorphismsBoundaryless :
    boundaryless.IsClosedUnderIsomorphisms (C := Mfld.{u} 𝕜 n)

/-- Every continuous linear equivalence is a uniform isomorphism.
TODO: move to another file. -/
@[simps]
def _root_.ContinuousLinearEquiv.toUniformEquiv {R₁ : Type*} {R₂ : Type*} [Semiring R₁]
    [Semiring R₂] {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] {E₁ : Type*} {E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : UniformEquiv E₁ E₂ where
  toFun := e
  invFun := e.symm
  uniformContinuous_toFun := e.toContinuousLinearMap.uniformContinuous
  uniformContinuous_invFun := e.symm.toContinuousLinearMap.uniformContinuous
  left_inv x := by simp
  right_inv x := by simp

instance [NeZero n] : banach.IsClosedUnderIsomorphisms (C := Mfld.{u} 𝕜 n) :=
  ⟨fun {M N} i ↦ .rec (Or.inl ∘ @(diffeomorphOfIso i).symm.isEmpty) <| fun _ ↦ by
    refine or_not.imp_right <| (fun ⟨x⟩ ↦ ?_) ∘ not_isEmpty_iff.1
    have e : N.modelVectorSpace ≃L[𝕜] M.modelVectorSpace :=
      (diffeomorphOfIso i).symm.mfderivToContinuousLinearEquiv NeZero.out x
    exact e.toUniformEquiv.completeSpace_iff.2 ‹_›⟩

instance [NeZero n] : finiteDimensional.IsClosedUnderIsomorphisms (C := Mfld.{u} 𝕜 n) :=
  ⟨fun {M N} i ↦ .rec (Or.inl ∘ @(diffeomorphOfIso i).symm.isEmpty) <| fun _ ↦ by
    refine or_not.imp_right <| (fun ⟨x⟩ ↦ ?_) ∘ not_isEmpty_iff.1
    have e : N.modelVectorSpace ≃L[𝕜] M.modelVectorSpace :=
      (diffeomorphOfIso i).symm.mfderivToContinuousLinearEquiv NeZero.out x
    exact e.symm.finiteDimensional⟩

end ClosedUnderIsomorphisms

section Products

/-- A choice of terminal object in the category of manifolds, given by `PUnit`. -/
abbrev pt : Mfld 𝕜 n := ⟨PUnit, 𝓘(𝕜, PUnit)⟩

/-- The choice `FinDimMfld.pt` of terminal object is indeed terminal. -/
def isTerminalPt : IsTerminal (pt : Mfld 𝕜 n) where
  lift s := ofHom (.const (default : PUnit))

/-- An explicit choice of product in the category of manifolds, given by the product of the
underlying types and models with corners. -/
protected abbrev prod (M N : Mfld.{u} 𝕜 n) : Mfld.{u} 𝕜 n :=
  ⟨M × N, M.modelWithCorners.prod N.modelWithCorners⟩

/-- The first projection realising `M.prod N` as the product of `M` and `N`. -/
def prodFst {M N : Mfld 𝕜 n} : M.prod N ⟶ M := ofHom .fst

/-- The second projection realising `M.prod N` as the product of `M` and `N`. -/
def prodSnd {M N : Mfld 𝕜 n} : M.prod N ⟶ N := ofHom .snd

/-- An explicit binary fan of `M` and `N` given by `M.prod N`. -/
def prodBinaryFan (M N : Mfld 𝕜 n) : BinaryFan N M :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit. -/
def prodBinaryFanIsLimit (M N : Mfld 𝕜 n) : IsLimit (prodBinaryFan N M) where
  lift c := ofHom <| .prodMk (hom <| BinaryFan.fst c) (hom <| BinaryFan.snd c)
  fac := by rintro c (_ | _) <;> dsimp [prodBinaryFan, prodFst] <;> ext <;> rfl
  uniq c f h := by
    ext x; refine Prod.ext ?_ ?_
    · exact CategoryTheory.congr_fun (h ⟨WalkingPair.left⟩) x
    · exact CategoryTheory.congr_fun (h ⟨WalkingPair.right⟩) x

instance : HasFiniteProducts (Mfld 𝕜 n) := by
  refine @hasFiniteProducts_of_has_binary_and_terminal _ _ ?_ isTerminalPt.hasTerminal
  exact @hasBinaryProducts_of_hasLimit_pair _ _ ⟨⟨_, prodBinaryFanIsLimit _ _⟩⟩

end Products

end Mfld
