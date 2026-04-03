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
* `EuclOp.toFinDimMfld`: the inclusion functor `EuclOp ⥤ FinDimMfld ℝ ∞` from open subsets of
  euclidean spaces to manifolds
* `EuclOp.toFinDimMfld` exhibits `EuclOp` as a dense sub-site of `FinDimMfld ℝ ∞`.

## TODO
* Show that `Functor.IsDenseSubsite` is closed under compositions, so that `CartSp` is a dense
  sub-site of `FinDimMfld ℝ ∞` too
-/

universe u

open CategoryTheory ContDiff TopologicalSpace Topology Set Manifold

namespace FinDimMfld

/-- On any open subset `u` of a manifold `M`, the diffeology derived from the manifold structure on
`u` and the subspace diffeology coming from the diffeology on `M` agree.
TODO: move somewhere else. -/
lemma _root_.IsManifold.toDiffeology_eq_subtype {E : Type*} [NormedAddCommGroup E]
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
    ⋃ (v : _) (f : v ⟶ u) (_ : s f), range f = univ}
  pullback u v g s hs := by
    obtain _ | _ := isEmpty_or_nonempty v
    · exact ⟨⊥, ⟨fun _ _ ↦ False.elim, Subsingleton.elim _ _⟩, fun _ _ ↦ False.elim⟩
    have _ := Nonempty.map g.hom ‹_›
    use fun k ↦ {f | (∃ (k : _) (f' : k ⟶ u), s f' ∧ range (g.hom.1 ∘ f.hom.1) ⊆ range f')
      ∧ @IsOpenInduction _ _ (IsManifold.toDiffeology k.obj.modelWithCorners _)
      (IsManifold.toDiffeology v.obj.modelWithCorners _) f}
    refine ⟨⟨fun k f hf ↦ hf.2, ?_⟩, ?_⟩
    · refine iUnion_eq_univ_iff.2 fun x ↦ ?_
      let ⟨w,hw⟩ := iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := mem_iUnion₂.1 hw
      let _ := IsManifold.toDiffeology u.1.modelWithCorners u
      let _ := IsManifold.toDiffeology v.1.modelWithCorners v
      let _ := IsManifold.toDiffeology w.1.modelWithCorners w
      use .mkOfOpen ⟨_, (hs.1 _ _ hf).isOpen_range'.preimage g.hom.2.continuous⟩
      refine mem_iUnion₂.2 ⟨⟨_, contMDiff_subtype_val (I := v.1.modelWithCorners)⟩, ?_⟩
      refine ⟨⟨⟨w, f, hf, ?_⟩, ?_⟩, ?_⟩
      · dsimp; rw [range_comp, Subtype.range_val]; simp
      · convert
          ((hs.1 _ _ hf).isOpen_range'.preimage g.hom.2.continuous).isOpenInduction_subtype_val'
        dsimp; rw [IsManifold.toDiffeology_eq_subtype]
      · change x ∈ range (Subtype.val : g ⁻¹' range f → _)
        simpa using hgx
    · intro k f ⟨⟨k', f', hf'⟩, hf⟩; use k'
      obtain _ | _ := isEmpty_or_nonempty k
      · use ⟨isEmptyElim, isEmptyElim⟩, f', hf'.1; ext x; exact isEmptyElim x
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
noncomputable def openCoverTopology : GrothendieckTopology (FinDimMfld ℝ ∞) :=
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
    let ⟨r', hr'⟩ := hr (hs'.1 _ _ hf)
    simp_rw [← image_univ, ← hr'.2.2, image_iUnion]
    refine iUnion_subset fun N' ↦ iUnion₂_subset fun g hg ↦ ?_
    refine subset_iUnion_of_subset N' <| subset_iUnion₂_of_subset (g ≫ f) ⟨?_, ?_⟩ ?_
    · exact hr'.1 _ _ hg
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
      subset_iUnion₂_of_subset f ⟨hr.1 _ _ hf, hr.2.1 N f hf⟩ subset_rfl
  · let _ := IsManifold.toDiffeology M.1.modelWithCorners M
    exact ⟨fun N f ↦ s f ∧ @IsOpenInduction _ _
      (IsManifold.toDiffeology N.1.modelWithCorners N) _ f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, h⟩

/-- `FinDimMfld ℝ ∞` is a concrete site, in that it is concrete with elements corresponding to
morphisms from the terminal object and carries a topology consisting entirely of jointly surjective
sieves. -/
noncomputable instance : openCoverTopology.{u}.IsConcreteSite
    (fun M N : FinDimMfld ℝ ∞ => ContMDiffMap M.1.modelWithCorners N.1.modelWithCorners M N ∞) where
  forgetNatIsoCoyoneda := NatIso.ofComponents fun M ↦ (InducedCategory.homEquiv.trans <|
    ContMDiffMap.equivDSmoothMap.trans <|
      @DSmoothMap.equivFnOfUnique _ M (_) (_) _ _ _).toIso.symm
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
  · exact fun x ↦ (show ⊤_ _ ⟶ M from f _ <| from_terminal_mem_of_mem _ hs ⟨.const x⟩) default
  · obtain _ | _ := isEmpty_or_nonempty N
    · exact isEmptyElim
    let _ := IsManifold.toDiffeology M.1.modelWithCorners M
    let _ := IsManifold.toDiffeology N.1.modelWithCorners N
    refine contMDiff_iff_dsmooth.2 <| dsmooth_iff_locally_dsmooth.2 fun x ↦ ?_
    let ⟨N', g, hg, hx⟩ := hs' x
    let _ := IsManifold.toDiffeology N'.1.modelWithCorners N'
    refine ⟨_, hg.2.isOpen_range, hx, ?_⟩
    rw [← hg.2.dsmooth_comp_iff_dsmooth_restrict]
    convert (f g hg.1).hom.2.dsmooth; ext1 x'
    specialize hf (𝟙 (⊤_ _)) (Y₂ := N') ⟨.const x'⟩
      (from_terminal_mem_of_mem _ hs ⟨.const (g x')⟩) hg.1 rfl
    exact congrFun (congrArg (Subtype.val ∘ InducedCategory.Hom.hom) hf) default
  · intro N' g hg; dsimp; ext x
    specialize hf (𝟙 (⊤_ _)) (Y₂ := N') ⟨.const x⟩
      (from_terminal_mem_of_mem _ hs ⟨.const (g x)⟩) hg rfl
    exact congrFun (congrArg (Subtype.val ∘ InducedCategory.Hom.hom) hf) default

end FinDimMfld

section EuclOpToFinDimMfld

/-- The embedding of `EuclOp` into `FinDimMfld  ℝ ∞`. -/
@[simps]
noncomputable def EuclOp.toFinDimMfld : EuclOp ⥤ FinDimMfld.{0} ℝ ∞ where
  obj u := .mk' u.2 𝓘(ℝ, Eucl u.1)
  map f := ⟨f, DSmooth.contMDiff <| by
    rw [dsmooth_iff_le_induced, IsManifold.toDiffeology_eq_subtype,
      IsManifold.toDiffeology_eq_subtype, IsManifold.toDiffeology_eq_euclideanDiffeology,
      IsManifold.toDiffeology_eq_euclideanDiffeology, ← dsmooth_iff_le_induced]
    exact f.2⟩

/-- `extChartAt I x` as a diffeological diffeomorphism. -/
@[simps]
noncomputable def extChartAtDDiffeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (x : M) :
    @DDiffeomorph (extChartAt I x).source (extChartAt I x).target
      (@instDiffeologicalSpaceSubtype _ (IsManifold.toDiffeology I M) _)
      (@instDiffeologicalSpaceSubtype _ euclideanDiffeology _) := by
    let _ := IsManifold.toDiffeology I M
    let _ := euclideanDiffeology (X := E)
    exact ⟨⟨(extChartAt _ x).mapsTo.restrict, (extChartAt _ x).symm_mapsTo.restrict,
      fun _ ↦ by ext1; simp [-extChartAt], fun _ ↦ by ext1; simp [-extChartAt]⟩, by
      have := (contMDiffOn_extChartAt (I := I)
        (x := x) (n := ∞)).dsmooth_restrict
      rw [← extChartAt_source I x,
        IsManifold.toDiffeology_eq_euclideanDiffeology] at this
      exact this.codRestrict _, by
      have := (contMDiffOn_extChartAt_symm (I := I)
        (x := x) (n := ∞)).dsmooth_restrict
      rw [IsManifold.toDiffeology_eq_euclideanDiffeology] at this
      exact this.codRestrict _⟩

set_option backward.isDefEq.respectTransparency false in
/-- Manifolds can be covered with open subsets of cartesian spaces. -/
instance : EuclOp.toFinDimMfld.IsCoverDense FinDimMfld.openCoverTopology := by
  constructor; intro M
  rw [FinDimMfld.openCoverTopology.mem_sieves_iff', eq_univ_iff_forall]
  intro x
  have : Nonempty M := ⟨x⟩
  simp_rw [mem_iUnion, exists_prop]
  use .mk' (Opens.interior (extChartAt M.1.modelWithCorners x).target) 𝓘(ℝ, M.1.modelVectorSpace)
  use ⟨(extChartAt _ x).symm ∘ (↑), (contMDiffOn_extChartAt_symm x).comp_contMDiff
    contMDiff_subtype_val fun x ↦ interior_subset x.2⟩
  dsimp
  refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
  · refine ⟨⟨_, ⟨toEuclidean '' interior (extChartAt M.1.modelWithCorners x).target, ?_⟩⟩,
      ⟨(mapsTo_image _ _).restrict toEuclidean, ?_⟩,
      ⟨(extChartAt M.1.modelWithCorners x).symm ∘ toEuclidean.symm ∘ Subtype.val, ?_⟩, ?_⟩
    · exact toEuclidean.isOpenMap _ isOpen_interior
    · dsimp; refine DSmooth.contMDiff ?_
      let _ : DiffeologicalSpace M.obj.modelVectorSpace := euclideanDiffeology
      rw [dsmooth_iff_le_induced, IsManifold.toDiffeology_eq_subtype,
        IsManifold.toDiffeology_eq_subtype, IsManifold.toDiffeology_eq_euclideanDiffeology,
        IsManifold.toDiffeology_eq_euclideanDiffeology, ← dsmooth_iff_le_induced]
      exact toEuclidean.contDiff.dsmooth.restrict (mapsTo_image _ _)
    · exact (contMDiffOn_extChartAt_symm x).comp_contMDiff
        (toEuclidean.symm.contDiff.contMDiff.comp <| by dsimp; exact contMDiff_subtype_val)
        fun y ↦ interior_subset <| by simpa only [toEuclidean.image_eq_preimage_symm] using y.2
    · ext x
      exact congrArg (extChartAt _ _).symm <| toEuclidean.symm_apply_apply _
  · let _ := IsManifold.toDiffeology M.1.modelWithCorners M
    let _ : DiffeologicalSpace M.obj.modelVectorSpace := euclideanDiffeology
    let e := extChartAtDDiffeomorph M.1.modelWithCorners x
    convert (IsOpen.isOpenInduction_subtype_val' ?_).comp <| e.symm.isOpenInduction.comp <|
      isOpen_interior.isOpenInduction_inclusion interior_subset
    · dsimp
      rw [IsManifold.toDiffeology_eq_subtype, IsManifold.toDiffeology_eq_euclideanDiffeology]
    · rw [extChartAt_source]; exact (chartAt _ _).open_source
  · use ⟨_, M.1.modelWithCorners.isInteriorPoint_iff.1 BoundarylessManifold.isInteriorPoint⟩
    change (extChartAt _ x).symm _ = x
    simp

instance EuclOp.toFinDimMfld_fullyFaithful : EuclOp.toFinDimMfld.FullyFaithful where
  preimage {u v} f := ⟨f, by
    convert (ConcreteCategory.ofHom f.hom).2.dsmooth <;> unfold toFinDimMfld
      <;> rw [IsManifold.toDiffeology_eq_subtype, IsManifold.toDiffeology_eq_euclideanDiffeology]⟩

instance : EuclOp.toFinDimMfld.Full := EuclOp.toFinDimMfld_fullyFaithful.full

instance : EuclOp.toFinDimMfld.Faithful := EuclOp.toFinDimMfld_fullyFaithful.faithful

/-- `EuclOp.toFinDimMfld` exhibits `EuclOp` as a dense sub-site of `FinDimMfld ℝ ∞` with respect to
the open cover topologies.
In particular, the sheaf topoi of the two sites are equivalent via `IsDenseSubsite.sheafEquiv`. -/
instance : EuclOp.toFinDimMfld.IsDenseSubsite
    EuclOp.openCoverTopology FinDimMfld.openCoverTopology where
  functorPushforward_mem_iff {u} s := by
    rw [EuclOp.openCoverTopology.mem_sieves_iff', FinDimMfld.openCoverTopology.mem_sieves_iff']
    refine Eq.congr_left (subset_antisymm ?_ ?_)
    · refine iUnion_subset fun M ↦ iUnion₂_subset fun f hf ↦ ?_
      obtain ⟨v, g, h, hg, rfl⟩ := hf.1; replace hf := hf.2
      refine range_subset_iff.2 fun x : M ↦ ?_
      change g (h x) ∈ _
      have : Nonempty M := ⟨x⟩
      let e := extChartAtDDiffeomorph M.1.modelWithCorners x
      let _ := IsManifold.toDiffeology M.1.modelWithCorners M
      let _ := euclideanDiffeology (X := M.1.modelVectorSpace)
      have hi : IsOpenInduction (Subtype.val ∘ e.symm ∘ (mapsTo_iff_subset_preimage.2 <|
          interior_subset.trans_eq <| toEuclidean.image_eq_preimage_symm _).restrict) := by
        refine (IsOpen.isOpenInduction_subtype_val' ?_).comp <| e.symm.isOpenInduction.comp <|
          toEuclidean.symm.toDDiffeomorph.isOpenInduction.restrict isOpen_interior _
        rw [extChartAt_source]; exact (chartAt _ _).open_source
      let _ := IsManifold.toDiffeology (EuclOp.toFinDimMfld.obj u).obj.modelWithCorners
        (EuclOp.toFinDimMfld.obj u)
      let _ := IsManifold.toDiffeology (EuclOp.toFinDimMfld.obj v).obj.modelWithCorners
        (EuclOp.toFinDimMfld.obj v)
      have hh := (ConcreteCategory.ofHom h.hom).2.dsmooth
      unfold EuclOp.toFinDimMfld at hf hh
      rw [IsManifold.toDiffeology_eq_subtype,
        IsManifold.toDiffeology_eq_euclideanDiffeology ] at hf hh
      refine mem_iUnion_of_mem ⟨_, ⟨interior <|
        toEuclidean '' (extChartAt M.1.modelWithCorners x).target, isOpen_interior⟩⟩ ?_
      refine mem_iUnion₂_of_mem (i := ⟨_, hh.comp hi.dsmooth⟩ ≫ g)
        ⟨s.downward_closed hg _, hf.comp hi⟩ ?_
      use ⟨toEuclidean (extChartAt M.1.modelWithCorners x x),
        toEuclidean.isOpenMap.image_interior_subset _ <| mem_image_of_mem toEuclidean <|
          M.1.modelWithCorners.isInteriorPoint_iff.1 BoundarylessManifold.isInteriorPoint⟩
      exact congr_arg (g ∘ h) (by simp : (extChartAt _ _).symm _ = x)
    · refine iUnion_subset fun v ↦ iUnion₂_subset fun f hf ↦ subset_iUnion_of_subset _ <|
        subset_iUnion₂_of_subset (EuclOp.toFinDimMfld.map f) ⟨?_, ?_⟩ subset_rfl
      · exact ⟨v, f, 𝟙 _, hf.1, (Category.id_comp _).symm⟩
      · convert hf.2 <;> unfold EuclOp.toFinDimMfld <;>
          rw [IsManifold.toDiffeology_eq_subtype, IsManifold.toDiffeology_eq_euclideanDiffeology]

end EuclOpToFinDimMfld
