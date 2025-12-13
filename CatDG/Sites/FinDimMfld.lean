import CatDG.ForMathlib.FinDimMfld
import CatDG.Sites.EuclOp

/-!
# The category `FinDimMfld ℝ n` as a site

In this file we equip the category `FinDimMfld ℝ ∞` of finite-dimensional, Hausdorff,
paracompact smooth real manifolds without boundary with the Grothendieck topology consisting of all
sieves that contain a family of jointly surjective open smooth embeddings, also called the
"open cover topology" because it equivalently consists of all sieves that contain
the family of inclusions corresponding to an open cover. We also show that
this topology is subcanonical.

Currently we only do this over `ℝ` and for smoothness degree `∞` because smooth embeddings are not
defined in mathlib yet; we use diffeological inductions instead, which are equivalent to smooth
embeddings but only available in the case of `ℝ` and `∞`. Once smooth embeddings are defined,
it should hopefully be easy to rephrase this in terms of smooth embeddings and generalise it.

## Main definitions / results:
* `FinDimMfld.openCoverCoverage`: the open cover coverage on `FinDimMfld ℝ ∞`, consisting of all
  jointly surjective families of open inductions
* `FinDimMfld.openCoverTopology`: the open cover topology on `FinDimMfld ℝ ∞`, consisting of all
  sieves containing a jointly surjective family of open inductions
* `FinDimMfld ℝ ∞` with the open cover topology is a concrete site
* the open cover topology on `FinDimMfld ℝ ∞` is subcanonical

## TODO
* `FinDimMfld ℝ ∞` has `EuclOp` (and hence also `CartSp`) as a dense sub-site
-/

universe u

open CategoryTheory ContDiff TopologicalSpace Topology Set

namespace FinDimMfld

/-- On any open subset `u` of a manifold `M`, the diffeology derived from the manifold structure on
`u` and the subspace diffeology coming from the diffeology on `M` agree.
TODO: move somewhere else. -/
lemma IsManifold.toDiffeology_eq_subtype {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (u : Opens M) :
    IsManifold.toDiffeology I u =
      @instDiffeologicalSpaceSubtype _ (IsManifold.toDiffeology I M) _ := by
  ext n p
  simp_rw [@(@isDInducing_subtype_val _ (_) _).isPlot_iff, isPlot_iff_contMDiff]
  refine ⟨contMDiff_subtype_val.comp, forall_imp fun x h ↦ ?_⟩
  simpa [contMDiffAt_iff, ← IsInducing.subtypeVal.continuousAt_iff, u.chartAt_eq] using h

/-- The open cover coverage on `FinDimMfld ℝ ∞`, consisting of all coverings by open smooth
embeddings.
Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
used instead. -/
def openCoverCoverage : Coverage (FinDimMfld ℝ ∞) where
  coverings u := {s | (∀ (v : _) (f : v ⟶ u), s f →
    @IsOpenInduction _ _ (IsManifold.toDiffeology v.obj.modelWithCorners _)
      (IsManifold.toDiffeology u.obj.modelWithCorners _) f) ∧
    ⋃ (v : _) (f ∈ s (Y := v)), range f = univ}
  pullback u v g s hs := by
    use fun k ↦ {f | (∃ (k : _) (f' : k ⟶ u), s f' ∧ range (g.1 ∘ f.1) ⊆ range f')
      ∧ @IsOpenInduction _ _ (IsManifold.toDiffeology k.obj.modelWithCorners _)
      (IsManifold.toDiffeology v.obj.modelWithCorners _) f}
    refine ⟨⟨fun k f hf ↦ hf.2, ?_⟩, ?_⟩
    · refine iUnion_eq_univ_iff.2 fun x ↦ ?_
      let ⟨w,hw⟩ := iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := mem_iUnion₂.1 hw
      let _ := IsManifold.toDiffeology u.1.modelWithCorners u
      let _ := IsManifold.toDiffeology v.1.modelWithCorners v
      let _ := IsManifold.toDiffeology w.1.modelWithCorners w
      use .mkOfOpen ⟨_, (hs.1 _ _ hf).isOpen_range'.preimage g.2.continuous⟩
      refine mem_iUnion₂.2 ⟨⟨_, contMDiff_subtype_val (I := v.1.modelWithCorners)⟩, ?_⟩
      refine ⟨⟨⟨w, f, hf, ?_⟩, ?_⟩, ?_⟩
      · dsimp; rw [range_comp, Subtype.range_val]; simp
      · dsimp; rw [IsManifold.toDiffeology_eq_subtype]
        exact ((hs.1 _ _ hf).isOpen_range'.preimage g.2.continuous).isOpenInduction_subtype_val'
      · change x ∈ range (Subtype.val : g ⁻¹' range f → _)
        simpa using hgx
    · intro k f ⟨⟨k', f', hf'⟩, hf⟩; use k'
      let _ := IsManifold.toDiffeology u.1.modelWithCorners u
      let _ := IsManifold.toDiffeology k.1.modelWithCorners k
      let _ := IsManifold.toDiffeology k'.1.modelWithCorners k'
      let f'' := (DDiffeomorph.ofIsInduction (hs.1 k' f' hf'.1).1)
      use ⟨_, (f''.dsmooth_invFun.comp <| (ConcreteCategory.hom (f ≫ g)).2.dsmooth.subtype_mk
        (fun x ↦ hf'.2 (mem_range_self x))).contMDiff⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; exact congrArg Subtype.val <| f''.apply_symm_apply _

/-- The open cover grothendieck topology on `FinDimMfld ℝ ∞`. -/
def openCoverTopology : GrothendieckTopology (FinDimMfld ℝ ∞) :=
  openCoverCoverage.toGrothendieck

/-- A sieve belongs to `FinDimMfld.openCoverTopology` iff it contains a presieve from
`FinDimMfld.openCoverCoverage`. -/
lemma openCoverTopology.mem_sieves_iff {M : FinDimMfld ℝ ∞} {s : Sieve M} :
    s ∈ openCoverTopology M ↔ ∃ r, r ≤ s.arrows ∧ r ∈ openCoverCoverage M := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr⟩ ↦ Coverage.mem_toGrothendieck_sieves_of_superset _ hr.1 hr.2⟩
  induction h with
  | of N s hs =>
    exact ⟨s, Sieve.le_generate s, hs⟩
  | top N =>
    let _ := IsManifold.toDiffeology N.1.modelWithCorners N
    refine ⟨fun M' f ↦ @IsOpenInduction _ _ (IsManifold.toDiffeology M'.1.modelWithCorners M') _ f,
      le_top, fun _ f hf ↦ hf, ?_⟩
    exact univ_subset_iff.1 <| subset_iUnion_of_subset N <|
        subset_iUnion₂_of_subset (𝟙 N) isOpenInduction_id (range_id.symm.subset)
  | transitive N s r _ _ hs hr =>
    let ⟨s', hs'⟩ := hs
    let _ := IsManifold.toDiffeology N.1.modelWithCorners N
    refine ⟨fun M' f ↦ r f ∧ @IsOpenInduction _ _
      (IsManifold.toDiffeology M'.1.modelWithCorners M') _ f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, ?_⟩
    rw [← univ_subset_iff, ← hs'.2.2]
    refine iUnion_subset fun M' ↦ iUnion₂_subset fun f hf ↦ ?_
    let ⟨r', hr'⟩ := hr (hs'.1 _ hf)
    simp_rw [← image_univ, ← hr'.2.2, image_iUnion]
    refine iUnion_subset fun N' ↦ iUnion₂_subset fun g hg ↦ ?_
    refine subset_iUnion_of_subset N' <| subset_iUnion₂_of_subset (g ≫ f) ⟨?_, ?_⟩ ?_
    · exact hr'.1 _ hg
    · let _ := IsManifold.toDiffeology M'.1.modelWithCorners M'
      let _ := IsManifold.toDiffeology N'.1.modelWithCorners N'
      exact (hs'.2.1 _ _ hf).comp (hr'.2.1 _ _ hg)
    · rw [← range_comp, image_univ]; rfl

/- A sieve belongs to `FinDimMfld.openCoverTopology` iff the open inductions in it are jointly
surjective. -/
lemma openCoverTopology.mem_sieves_iff' {M : FinDimMfld ℝ ∞} {s : Sieve M} :
    s ∈ openCoverTopology M ↔ ⋃ (N) (f : N ⟶ M) (_ : s f ∧ @IsOpenInduction _ _
      (IsManifold.toDiffeology N.1.modelWithCorners N)
        (IsManifold.toDiffeology M.1.modelWithCorners M) f), range f = univ := by
  refine mem_sieves_iff.trans ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← univ_subset_iff, ← hr.2.2]
    exact iUnion_subset fun N ↦ iUnion₂_subset fun f hf ↦ subset_iUnion_of_subset N <|
      subset_iUnion₂_of_subset f ⟨hr.1 _ hf, hr.2.1 N f hf⟩ subset_rfl
  · let _ := IsManifold.toDiffeology M.1.modelWithCorners M
    exact ⟨fun N f ↦ s f ∧ @IsOpenInduction _ _
      (IsManifold.toDiffeology N.1.modelWithCorners N) _ f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, h⟩

/-- `FinDimMfld ℝ ∞` is a concrete site, in that it is concrete with elements corresponding to
morphisms from the terminal object and carries a topology consisting entirely of jointly surjective
sieves. -/
noncomputable instance : openCoverTopology.{u}.IsConcreteSite where
  forgetNatIsoCoyoneda := NatIso.ofComponents fun M ↦
    (ContMDiffMap.equivDSmoothMap.trans <| @DSmoothMap.equivFnOfUnique _ M (_) (_) _ _ _).toIso.symm
  forgetNatIsoCoyoneda_apply := rfl
  isJointlySurjective_of_mem hs := by
    rw [openCoverTopology.mem_sieves_iff] at hs
    obtain ⟨r, hr⟩ := hs
    exact .mono hr.1 <| Presieve.isJointlySurjective_iff_iUnion_range_eq_univ.2 hr.2.2

open GrothendieckTopology.IsConcreteSite in
/-- `FinDimMfld ℝ ∞` is a subcanonical site, i.e. all representable presheaves on it are sheaves. -/
instance : openCoverTopology.{u}.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun M N s hs ↦ ?_
  refine (isSeparated_yoneda_obj _ M s hs).isSheafFor fun f hf ↦ ?_
  let hs' := hs; simp_rw [openCoverTopology.mem_sieves_iff', eq_univ_iff_forall, mem_iUnion] at hs'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact fun x ↦ (show ⊤_ _ ⟶ M from f _ <| from_terminal_mem_of_mem _ hs (.const x)) default
  · let _ := IsManifold.toDiffeology M.1.modelWithCorners M
    let _ := IsManifold.toDiffeology N.1.modelWithCorners N
    refine contMDiff_iff_dsmooth.2 <| dsmooth_iff_locally_dsmooth.2 fun x ↦ ?_
    let ⟨N', g, hg, hx⟩ := hs' x
    let _ := IsManifold.toDiffeology N'.1.modelWithCorners N'
    refine ⟨_, hg.2.isOpen_range, hx, ?_⟩
    rw [← hg.2.dsmooth_comp_iff_dsmooth_restrict]
    convert (f g hg.1).2.dsmooth; ext1 x'
    specialize hf (𝟙 (⊤_ _)) (Y₂ := N') (.const x')
      (from_terminal_mem_of_mem _ hs (.const (g x'))) hg.1 rfl
    exact congrFun (congrArg Subtype.val hf) (default : ⊤_ FinDimMfld ℝ ∞)
  · intro N' g hg; dsimp; ext x
    specialize hf (𝟙 (⊤_ _)) (Y₂ := N') (.const x)
      (from_terminal_mem_of_mem _ hs (.const (g x))) hg rfl
    exact congrFun (congrArg Subtype.val hf) (default : ⊤_ FinDimMfld ℝ ∞)

end FinDimMfld
