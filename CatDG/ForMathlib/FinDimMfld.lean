import CatDG.Diffeology.Manifolds
import CatDG.ForMathlib.Mfld
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The category of finite-dimensional manifolds
Results on the category `FinDimMfld 𝕜 n` of finite-dimensional, Hausdorff, sigma-compact manifolds
without boundary, for any given smoothness degree `n : WithTop ℕ∞` and nontrivially normed ground
field `𝕜`.

This category is already defined in `CatDG.ForMathlib.Mfld` as a full subcategory of `Mfld 𝕜 n`
and equipped with forgetful functors to various categories there; here we only prove more specific
results.

## Main definitions / results
* `FinDimMfld 𝕜 n`: the category of all finite-dimensional Hausdorff σ-compact Cⁿ manifolds without
  boundary over a fixed ground field `𝕜`.
* `FinDimMfld 𝕜 n` has all finite products.
* `FinDimMfld.mono_iff_injective`: morphisms in `FinDimMfld 𝕜 n` are monomorphisms iff they are
  injective
* `FinDimMfld.epi_iff_denseRange`: morphisms in `FinDimMfld ℝ ∞` are epimorphisms iff their range is
  dense

## TODOs
* show that `FinDimMfld 𝕜 n` is essentially small
* generalise `epi_iff_denseRange` to smoothness degrees in `ℕ∞`
* can anything interesting be said about extremal monomorphisms / epimorphisms?
* define the embedding into `(CommAlgCat ℝ)ᵒᵖ` and show that it is fully faithful. Fullness will
  likely require a stronger Whitney embedding theorem than currently is in mathlib.
-/

universe u

open CategoryTheory ConcreteCategory Manifold ContDiff Function Limits TopologicalSpace

initialize_simps_projections Mfld (+carrier, +modelVectorSpace, +model, +modelWithCorners)

namespace FinDimMfld

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}

protected abbrev mk' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} (M : Type u)
    [TopologicalSpace M] {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type u}
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [ChartedSpace H M] [IsManifold I n M]
    [FiniteDimensional 𝕜 E] [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] :
    FinDimMfld 𝕜 n :=
  ⟨⟨M, I⟩, ⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩

/-- A choice of terminal object in the category of manifolds, given by `PUnit`. -/
abbrev pt : FinDimMfld 𝕜 n := .mk' PUnit 𝓘(𝕜, PUnit)

/-- The choice `FinDimMfld.pt` of terminal object is indeed terminal. -/
def isTerminalPt : IsTerminal (pt : FinDimMfld 𝕜 n) where
  lift s := ofHom (.const (default : PUnit))

/-- An explicit choice of product in the category of manifolds, given by the product of the
underlying types and models with corners. -/
protected abbrev prod (M N : FinDimMfld.{u} 𝕜 n) : FinDimMfld.{u} 𝕜 n :=
  .mk' (M × N) (M.obj.modelWithCorners.prod N.obj.modelWithCorners)

/-- The first projection realising `M.prod N` as the product of `M` and `N`. -/
def prodFst {M N : FinDimMfld 𝕜 n} : M.prod N ⟶ M := ofHom .fst

/-- The second projection realising `M.prod N` as the product of `M` and `N`. -/
def prodSnd {M N : FinDimMfld 𝕜 n} : M.prod N ⟶ N := ofHom .snd

/-- An explicit binary fan of `M` and `N` given by `M.prod N`. -/
def prodBinaryFan (M N : FinDimMfld 𝕜 n) : BinaryFan N M :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit. -/
def prodBinaryFanIsLimit (M N : FinDimMfld 𝕜 n) : IsLimit (prodBinaryFan N M) where
  lift c := ofHom <| .prodMk (hom <| BinaryFan.fst c) (hom <| BinaryFan.snd c)
  fac := by rintro c (_ | _) <;> dsimp [prodBinaryFan, prodFst] <;> ext <;> rfl
  uniq c f h := by
    ext x; refine Prod.ext ?_ ?_
    · exact CategoryTheory.congr_fun (h ⟨WalkingPair.left⟩) x
    · exact CategoryTheory.congr_fun (h ⟨WalkingPair.right⟩) x

instance : HasFiniteProducts (FinDimMfld 𝕜 n) := by
  refine @hasFiniteProducts_of_has_binary_and_terminal _ _ ?_ isTerminalPt.hasTerminal
  exact @hasBinaryProducts_of_hasLimit_pair _ _ ⟨⟨_, prodBinaryFanIsLimit _ _⟩⟩

-- TODO: figure out how to get this from more general instances
noncomputable instance : Unique (⊤_ (FinDimMfld 𝕜 n)) := by
  have : Unique ((forget (FinDimMfld 𝕜 n)).obj pt) := inferInstanceAs (Unique PUnit)
  exact ((forget _).mapIso (terminalIsTerminal.uniqueUpToIso isTerminalPt)).toEquiv.unique

lemma mono_iff_injective {M N : FinDimMfld.{u} 𝕜 n} (f : M ⟶ N) : Mono f ↔ Injective f := by
  refine ⟨fun hf x y h ↦ ?_, ConcreteCategory.mono_of_injective _⟩
  let x' : pt ⟶ M := ofHom (.const x)
  let y' : pt ⟶ M := ofHom (.const y)
  exact CategoryTheory.congr_fun (hf.right_cancellation x' y' <| by ext; exact h) default

lemma epi_iff_denseRange {M N : FinDimMfld.{0} ℝ ∞} (f : M ⟶ N) :
    Epi f ↔ DenseRange f := by
  refine ⟨not_imp_not.1 fun hf hf' ↦ ?_, fun hf ↦ ⟨fun g g' hg ↦ ?_⟩⟩
  · rw [DenseRange, ← compl_compl (Set.range _), ← interior_eq_empty_iff_dense_compl] at hf
    replace hf := Set.nonempty_iff_ne_empty.2 hf
    obtain ⟨x, hx⟩ := hf
    let ℝ' : FinDimMfld.{0} ℝ ∞:= .mk' ℝ 𝓘(ℝ, ℝ)
    let ⟨g, hg⟩ := exists_contMDiffMap_zero_one_of_isClosed N.obj.modelWithCorners (n := ⊤)
      (isClosed_closure (s := Set.range (hom f))) (isClosed_singleton (x := x)) (by simpa using hx)
    have hg' := hf'.left_cancellation (Z := ℝ') (ofHom g) (ofHom (.const 0))
      (by ext y; exact congrFun (Set.eqOn_range.1 <| hg.1.mono subset_closure) y)
    exact zero_ne_one ((CategoryTheory.congr_fun hg' x).symm.trans <| hg.2.1 (Set.mem_singleton _))
  · apply ConcreteCategory.coe_ext
    rw [← Set.eqOn_univ, ← hf.closure_range]
    refine Set.EqOn.closure ?_ (map_continuous _) (map_continuous _)
    exact Set.eqOn_range.2 <| congrArg (fun (f : M ⟶ _) ↦ ⇑(hom f)) hg

instance {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] (u : Opens X) :
    LocallyCompactSpace u :=
  u.2.locallyCompactSpace

instance {M : FinDimMfld ℝ ∞} : SecondCountableTopology M := by
  have := M.1.modelWithCorners.toHomeomorphTarget.secondCountableTopology
  exact ChartedSpace.secondCountable_of_sigmaCompact M.1.model M

instance {M : FinDimMfld ℝ ∞} : LocallyCompactSpace M := by
  have := M.1.modelWithCorners.toHomeomorphTarget.locallyCompactSpace_iff.2 <|
    M.1.modelWithCorners.range_eq_target ▸ M.1.modelWithCorners.isClosed_range.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace M.1.model M

noncomputable abbrev mkOfOpen {M : FinDimMfld ℝ ∞} (u : Opens M) :
    FinDimMfld ℝ ∞ :=
  .mk' u M.1.modelWithCorners

end FinDimMfld
