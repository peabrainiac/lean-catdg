import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Category.TopCat.Basic

/-!
# The category of finite-dimensional manifolds
We define the category of finite-dimensional, Hausdorff, sigma-compact manifolds without boundary,
for any given smoothness degree `n : WithTop ℕ∞` and nontrivially normed ground field `𝕜`.

So far, the only result we prove to test that the API is set up correctly is that the monomorphisms
in the category of finite-dimensional manifolds are precisely the injective functions.
-/

universe u

open CategoryTheory ConcreteCategory Manifold Function Limits

/-- The category of all finite-dimensional manifolds for a fixed ground field `𝕜` and
smoothness degree `n : WithTop ℕ∞`. Objects are the finite-dimensional sigma-compact Hausdorff
manifolds without boundary, morphisms are the Cⁿ maps. -/
structure FinDimMfld (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) where
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
  [finiteDimensional : FiniteDimensional 𝕜 modelVectorSpace]
  [t2Space : T2Space carrier]
  [sigmaCompactSpace : SigmaCompactSpace carrier]
  [boundaryless : BoundarylessManifold modelWithCorners carrier]

attribute [instance] FinDimMfld.topology FinDimMfld.normedAddCommGroup FinDimMfld.normedSpace
  FinDimMfld.modelTopology FinDimMfld.chartedSpace FinDimMfld.isManifold
  FinDimMfld.finiteDimensional FinDimMfld.t2Space FinDimMfld.sigmaCompactSpace
  FinDimMfld.boundaryless

initialize_simps_projections FinDimMfld (+carrier, +modelVectorSpace, +model, +modelWithCorners)

namespace FinDimMfld

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}

instance : CoeSort (FinDimMfld 𝕜 n) (Type u) :=
  ⟨FinDimMfld.carrier⟩

instance (𝕜 : Type*) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) : Category (FinDimMfld 𝕜 n) where
  Hom M N := ContMDiffMap M.modelWithCorners N.modelWithCorners M.carrier N.carrier n
  id M := ContMDiffMap.id
  comp f g := g.comp f

instance : ConcreteCategory.{u} (FinDimMfld 𝕜 n)
    (fun M N => ContMDiffMap M.modelWithCorners N.modelWithCorners M N n) where
  hom f := f
  ofHom f := f

@[simps]
instance : HasForget₂ (FinDimMfld 𝕜 n) TopCat where
  forget₂ := { obj M := .of M, map (f : ContMDiffMap _ _ _ _ _) := TopCat.ofHom f }

/-- A choice of terminal object in the category of manifolds, given by `PUnit`. -/
abbrev pt : FinDimMfld 𝕜 n := .mk PUnit 𝓘(𝕜, PUnit)

/-- The choice `FinDimMfld.pt` of terminal object is indeed terminal. -/
def isTerminalPt : IsTerminal (pt : FinDimMfld 𝕜 n) where
  lift s := ofHom (.const (default : PUnit))

/-- An explicit choice of product in the category of manifolds, given by the product of the
underlying types and models with corners. -/
protected abbrev prod (M N : FinDimMfld.{u} 𝕜 n) : FinDimMfld.{u} 𝕜 n :=
  ⟨M × N, M.modelWithCorners.prod N.modelWithCorners⟩

/-- The first projection realising `M.prod N` as the product of `M` and `N`. -/
def prodFst {M N : FinDimMfld 𝕜 n} : M.prod N ⟶ M := ofHom .fst

/-- The second projection realising `M.prod N` as the product of `M` and `N`. -/
def prodSnd {M N : FinDimMfld 𝕜 n} : M.prod N ⟶ N := ofHom .snd

/-- An explicit binary fan of `M` and `N` given by `M.prod N`. -/
def prodBinaryFan (M N : FinDimMfld 𝕜 n) : BinaryFan N M :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit. -/
def prodBinaryFanIsLimit (M N : FinDimMfld 𝕜 n) : IsLimit (prodBinaryFan N M) where
  lift c := ofHom <| .prodMk (BinaryFan.fst c) (BinaryFan.snd c)
  fac := by rintro c (_ | _) <;> dsimp [prodBinaryFan, prodFst] <;> ext <;> rfl
  uniq c f h := by
    ext x; refine Prod.ext ?_ ?_
    · exact CategoryTheory.congr_fun (h ⟨WalkingPair.left⟩) x
    · exact CategoryTheory.congr_fun (h ⟨WalkingPair.right⟩) x

instance : HasFiniteProducts (FinDimMfld 𝕜 n) := by
  refine @hasFiniteProducts_of_has_binary_and_terminal _ _ ?_ isTerminalPt.hasTerminal
  exact @hasBinaryProducts_of_hasLimit_pair _ _ ⟨⟨_, prodBinaryFanIsLimit _ _⟩⟩

lemma mono_iff_injective {M N : FinDimMfld.{u} 𝕜 n} (f : M ⟶ N) : Mono f ↔ Injective f := by
  refine ⟨fun hf x y h ↦ ?_, ConcreteCategory.mono_of_injective _⟩
  let x' : pt ⟶ M := ofHom (.const x)
  let y' : pt ⟶ M := ofHom (.const y)
  exact CategoryTheory.congr_fun (hf.right_cancellation x' y' <| by ext; exact h) default

end FinDimMfld
