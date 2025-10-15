import CatDG.Diffeology.LocallyModelled
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Diffeological manifolds
Some lemmas and theorems on manifolds as diffeological spaces, as defined in
`CatDG.Diffeology.LocallyModelled`. The main purpose of this file is to show how this
relates to the notion of smooth manifolds defined in mathlib , i.e. that those are indeed
equivalent.
-/

open Set

open scoped Manifold ContDiff

open OpenPartialHomeomorph in
/-- The diffeology defined by a manifold structure on M, with the plots given by the maps
that are smooth in the sense of mathlib's `ContMDiff`-API.
This can not be an instance because `IsManifold I M` depends on `I` while
`DiffeologicalSpace M` does not, and because it would probably lead to instance diamonds on
things like products even if some workaround was found. -/
def IsManifold.toDiffeology {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    DiffeologicalSpace M :=
  DiffeologicalSpace.mkOfPlotsOn {
    isPlotOn := fun {n u} _ p ↦ ContMDiffOn (𝓡 n) I ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contMDiffOn_congr h
    isPlot := fun {n} p ↦ ContMDiff (𝓡 n) I ∞ p
    isPlotOn_univ := contMDiffOn_univ
    isPlot_const := fun _ ↦ contMDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf.contMDiffOn h.subset_preimage
    locality := fun _ _ h ↦ fun x hxu ↦ by
      let ⟨v,hv,hxv,hv'⟩ := h x hxu
      exact ((hv' x hxv).contMDiffAt (hv.mem_nhds hxv)).contMDiffWithinAt
  }

/-- The plots of a manifold are by definition precisely the smooth maps. -/
lemma isPlot_iff_contMDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M]
    {n : ℕ} {p : Eucl n → M} : IsPlot[m.toDiffeology] p ↔ ContMDiff (𝓡 n) I ∞ p := Iff.rfl

lemma IsManifold.toDiffeology_eq_euclideanDiffeology {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (instIsManifoldModelSpace (I := 𝓘(ℝ,E))).toDiffeology = euclideanDiffeology := by
  ext n p; exact contMDiff_iff_contDiff

def ModelWithCorners.toHomeomorphTarget {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : H ≃ₜ I.target where
  toFun x := ⟨I x,I.map_source (I.source_eq ▸ mem_univ x)⟩
  invFun y := I.invFun y
  left_inv := I.left_inv
  right_inv := fun x ↦ Subtype.ext <| I.right_inv (I.target_eq ▸ x.2)
  continuous_toFun := by have := I.continuous_toFun; fun_prop
  continuous_invFun := by have := I.continuous_invFun; fun_prop

/-- The D-topology on a manifold is always at least as fine as the usual topology. -/
lemma IsManifold.dTop_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [tM : TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M] :
    DTop[m.toDiffeology] ≤ tM :=
  TopologicalSpace.le_def.2 fun _ hu _ _ hp ↦ IsOpen.preimage (hp.continuous) hu

/-- If the subspace topology and D-topology agree on the set `H` that the manifold is modelled on,
the topology of the manifold agrees with the D-topology as well.-/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [tH : TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [@DTopCompatible I.target _ <| @instDiffeologicalSpaceSubtype _ euclideanDiffeology _]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M] :
    let _ := m.toDiffeology; DTopCompatible M := let _ := m.toDiffeology; ⟨by
  let dE := euclideanDiffeology (X := E); let dH := dE.induced I
  have : DTopCompatible H := ⟨by
    dsimp [dH]; rw [show ↑I = (↑) ∘ I.toHomeomorphTarget by rfl,←dE.induced_compose,
      dTop_induced_comm (by convert isOpen_univ; exact Equiv.range_eq_univ _),dTop_eq _,
      Homeomorph.induced_eq]⟩
  ext u; refine ⟨fun h ↦ ?_,fun hu n p hp ↦ IsOpen.preimage (hp.continuous) hu⟩
  refine isOpen_iff_mem_nhds.2 fun x hxu ↦ mem_nhds_iff.2
    ⟨_,inter_subset_right,?_,mem_chart_source H x,hxu⟩
  have _ := (chartAt H x).open_target.dTopCompatible
  refine Subtype.image_preimage_val _ _ ▸ (chartAt H x).open_source.isOpenMap_subtype_val _ ?_
  rw [←(chartAt H x).toHomeomorphSourceTarget.symm.isOpen_preimage]
  simp_rw [←dTop_eq (chartAt H x).target]; rw [isOpen_iff_preimages_plots]; intro n p hp
  simp_rw [←preimage_comp,Function.comp_assoc]
  rw [isOpen_iff_preimages_plots] at h; refine h n _ ?_; rw [isPlot_iff_contMDiff]
  replace hp := (isPlot_induced_iff.1 <| isPlot_induced_iff.1 hp).contMDiff (n := ∞)
  replace hp := (contMDiffOn_model_symm).comp_contMDiff hp fun x ↦ mem_range_self _
  rw [←Function.comp_assoc,I.symm_comp_self,Function.id_comp] at hp
  exact (contMDiffOn_chart_symm (x := x)).comp_contMDiff hp fun x ↦ (p x).2⟩

/-- In particular, the D-topology agrees with the standard topology on all manifolds
modelled on a "boundaryless" model.
TODO: It would be nice to have this (and all lemmas depending on it) for all boundaryless
manifolds in the sense of `BoundarylessManifold`, such as manifolds with corners whose
boundary just happens to be empty, but that would require either redoing the above lemma
in slightly greater generality or passing from manifolds with empty boundary to manifolds
modelled on a boundaryless model, both of which sound like a lot of work for something that
is not a high priority. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [hI : I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M] :
    let _ := m.toDiffeology; DTopCompatible M := by
  let _ := m.toDiffeology; let _ := euclideanDiffeology (X := E)
  have : DTopCompatible I.target :=
    I.target_eq.trans hI.range_eq_univ ▸ isOpen_univ.dTopCompatible
  infer_instance

/-- Every smooth map between manifolds is also D-smooth, i.e. this construction defines a
functor of concrete categories. -/
theorem ContMDiff.dsmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [m' : IsManifold I' ∞ N]
    {f : M → N} (hf : ContMDiff I I' ∞ f) : DSmooth[m.toDiffeology,m'.toDiffeology] f :=
  fun _ _ ↦ hf.comp

/-- Every map between manifolds that is smooth on a subset is also smooth diffeologically
with respect to the subspace diffeology. -/
theorem ContMDiffOn.dsmooth_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [m' : IsManifold I' ∞ N]
    {f : M → N} {s : Set M} (hf : ContMDiffOn I I' ∞ f s) :
    let _ := m.toDiffeology; let _ := m'.toDiffeology; DSmooth (s.restrict f) := by
  let _ := m.toDiffeology; let _ := m'.toDiffeology
  refine fun n p hp ↦ ?_
  rw [restrict_eq,Function.comp_assoc]
  exact hf.comp_contMDiff hp fun x ↦ (p x).2

open OpenPartialHomeomorph in
/-- Every D-smooth map from a boundaryless manifold to another manifold is also smooth.
This could probably be proven in quite a lot greater generality. -/
theorem IsOpen.dsmooth_iff_smoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M]
    [hI : I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} (N : Type*)
    [TopologicalSpace N] [ChartedSpace H' N] [m' : IsManifold I' ∞ N]
    {f : M → N} {s : Set M} (hs : IsOpen s) : let _ := m.toDiffeology;
    let _ := m'.toDiffeology; DSmooth (s.restrict f) ↔ ContMDiffOn I I' ∞ f s := by
  let _ := m.toDiffeology; let _ := m'.toDiffeology
  refine ⟨fun hf x hxs ↦ ?_,ContMDiffOn.dsmooth_restrict⟩
  -- TODO
  sorry

open OpenPartialHomeomorph in
/-- Every D-smooth map from a boundaryless manifold to another manifold is also smooth.
This could probably be proven in quite a lot greater generality. -/
theorem DSmooth.smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M]
    [hI : I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [m' : IsManifold I' ∞ N]
    {f : M → N} (hf : DSmooth[m.toDiffeology,m'.toDiffeology] f) : ContMDiff I I' ∞ f := by
  let _ := m.toDiffeology; let _ := m'.toDiffeology
  intro x; let x' := toEuclidean (extChartAt I x x); let n := Module.finrank ℝ E
  let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 (toEuclidean.isOpenMap _ (isOpen_extChartAt_target x))
    x' <| mem_image_of_mem _ <| (extChartAt I x).map_source (mem_extChartAt_source x)
  let e := (extChartAt I x).symm ∘ toEuclidean.symm ∘
    (univUnitBall.trans' (unitBallBall x' ε hε) rfl)
  have he : ContMDiff (𝓡 n) I ∞ e := (contMDiffOn_extChartAt_symm x).comp_contMDiff
    (toEuclidean.symm.contDiff.comp <| (contDiff_unitBallBall hε).comp
    contDiff_univUnitBall).contMDiff fun x'' ↦ (mem_image_equiv (f := toEuclidean.toEquiv)).1 <|
    hε' <| (univUnitBall.trans' (unitBallBall x' ε hε) rfl).map_source <| mem_univ _
  let e' := (univUnitBall.trans' (unitBallBall x' ε hε) rfl).symm ∘ toEuclidean ∘ extChartAt I x
  have he' : ContMDiffOn I (𝓡 n) ∞ e' _ :=
    (contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm hε).contDiffOn fun _ hx'' ↦
        mem_preimage.2 ((unitBallBall x' ε hε).symm.map_source hx'')).contMDiffOn.comp
      (toEuclidean.contDiff.contMDiff.comp_contMDiffOn <| contMDiffOn_extChartAt.mono <|
        inter_subset_right) inter_subset_left
  refine (((hf n _ he).comp_contMDiffOn he').congr (fun x'' hx'' ↦ ?_) x ?_).contMDiffAt ?_
  · simp_rw [e,e',Function.comp_apply]
    rw [(univUnitBall.trans' (unitBallBall x' ε hε) rfl).right_inv (by exact hx''.1),
      toEuclidean.symm_apply_apply,(extChartAt I x).left_inv (extChartAt_source I x ▸ hx''.2)]
  · exact ⟨Metric.mem_ball_self hε,mem_chart_source H x⟩
  · refine IsOpen.mem_nhds ?_ ⟨Metric.mem_ball_self hε,mem_chart_source H x⟩
    exact inter_comm _ _ ▸ extChartAt_source I x ▸ ContinuousOn.isOpen_inter_preimage
      (toEuclidean.continuous.comp_continuousOn (continuousOn_extChartAt x))
      (isOpen_extChartAt_source x) Metric.isOpen_ball

/-- A finite-dimensional, boundaryless smooth manifold with corners in the sense of `IsManifold`
is also a manifold in the sense of `IsDiffeologicalManifold`. -/
theorem IsManifold.isDiffeologicalManifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : IsManifold I ∞ M]
    [hI : I.Boundaryless] : @IsDiffeologicalManifold (Module.finrank ℝ E) M m.toDiffeology :=
  let _ := m.toDiffeology; let _ := euclideanDiffeology (X := E)
  ⟨fun x ↦ (dTop_eq M).symm ▸ ⟨_,isOpen_extChartAt_source x,mem_extChartAt_source x,
    (),_,toEuclidean.isOpenMap _ (isOpen_extChartAt_target x),⟨{
      toEquiv := ((extChartAt I x).trans' (toEuclidean.toEquiv.toPartialEquivOfImageEq
        (extChartAt I x).target _ rfl) rfl).toEquiv
      dsmooth_toFun := by
        dsimp [PartialEquiv.trans',PartialEquiv.toEquiv,-extChartAt]
        refine (toEuclidean.contDiff.dsmooth.comp ?_).subtype_mk _
        exact (toDiffeology_eq_euclideanDiffeology (E := E) ▸ (extChartAt_source I x).symm ▸
          (contMDiffOn_extChartAt (I := I) (x := x)).dsmooth_restrict:)
      dsmooth_invFun := by
        dsimp [PartialEquiv.trans',PartialEquiv.toEquiv,-extChartAt]
        refine DSmooth.subtype_mk ?_ _
        rw [←Function.comp_def (extChartAt I x).symm,←Function.comp_def _ Subtype.val,
          ←(mapsTo_image _ _).restrict_commutes _ _ _,←Function.comp_assoc]
        refine DSmooth.comp ?_ (toEuclidean.symm.contDiff.dsmooth.restrict _)
        exact (toEuclidean.symm_image_image (extChartAt I x).target).symm ▸
          (toDiffeology_eq_euclideanDiffeology (E := E) ▸
            (contMDiffOn_extChartAt_symm (I := I) x).dsmooth_restrict:)
    }⟩⟩⟩

-- TODO: move this and related lemmas to a more fitting place
open Classical in
@[simps]
noncomputable def PartialEquiv.fromEquivSourceTarget {α β : Type*} {s : Set α} {t : Set β}
    (e : s ≃ t) (a : s) : PartialEquiv α β where
  toFun := fun x ↦ if hx : x ∈ s then e ⟨x,hx⟩ else e a
  invFun := fun y ↦ if hy : y ∈ t then e.symm ⟨y,hy⟩ else a
  source := s
  target := t
  map_source' := fun _ hx ↦ by simp [hx]
  map_target' := fun _ hy ↦ by simp [hy]
  left_inv' := fun _ hx ↦ by simp [hx]
  right_inv' := fun _ hy ↦ by simp [hy]

@[simp]
lemma PartialEquiv.fromEquivSourceTarget_restrict {α β : Type*} {s : Set α} {t : Set β}
    (e : s ≃ t) (a : s) : s.restrict (fromEquivSourceTarget e a) = (↑) ∘ e := by
  ext x; simp

@[simp]
lemma PartialEquiv.fromEquivSourceTarget_symm_restrict {α β : Type*} {s : Set α} {t : Set β}
    (e : s ≃ t) (a : s) : t.restrict (fromEquivSourceTarget e a).symm = (↑) ∘ e.symm := by
  ext x; simp

@[simp]
lemma PartialEquiv.fromEquivSourceTarget_toEquiv {α β : Type*} {s : Set α} {t : Set β}
    (e : s ≃ t) (a : s) : (fromEquivSourceTarget e a).toEquiv = e := by
  ext x; simp only [PartialEquiv.toEquiv,fromEquivSourceTarget_apply,fromEquivSourceTarget_source,
    Subtype.coe_prop]; rfl

@[simps!]
noncomputable def OpenPartialHomeomorph.fromHomeomorphSourceTarget {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {t : Set β} (e : s ≃ₜ t) (hs : IsOpen s)
    (ht : IsOpen t) (a : s) : OpenPartialHomeomorph α β where
  toPartialEquiv := PartialEquiv.fromEquivSourceTarget e.toEquiv a
  open_source := hs
  open_target := ht
  continuousOn_toFun := by simp [continuousOn_iff_continuous_restrict,continuous_subtype_val]
  continuousOn_invFun := by simp [continuousOn_iff_continuous_restrict,continuous_subtype_val]

@[simp]
lemma OpenPartialHomeomorph.fromHomeomorphSourceTarget_toPartialEquiv {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {t : Set β} (e : s ≃ₜ t) (hs : IsOpen s)
    (ht : IsOpen t) (a : s) : (fromHomeomorphSourceTarget e hs ht a).toPartialEquiv =
    PartialEquiv.fromEquivSourceTarget e.toEquiv a := rfl

/-- Charted space structure of a diffeological manifold, consisting of all local diffeomorphisms
between `M` and `Eucl n`. -/
noncomputable def IsDiffeologicalManifold.toChartedSpace {M : Type*} [DiffeologicalSpace M] {n : ℕ}
    [hM : IsDiffeologicalManifold n M] : @ChartedSpace (Eucl n) _ M DTop := by
  let _ := @DTop M _; let _ : DTopCompatible M := ⟨rfl⟩; exact {
    atlas := {e | DSmooth e.toEquiv ∧ DSmooth e.toEquiv.symm}
    chartAt := fun x ↦ by
      have h := hM.locally_modelled x
      have hu := h.choose_spec.1; have hxu := h.choose_spec.2.1
      have hv := h.choose_spec.2.2.choose_spec.choose_spec.1
      have _ := hu.dTopCompatible; have _ := hv.dTopCompatible
      exact OpenPartialHomeomorph.fromHomeomorphSourceTarget
        (h.choose_spec.2.2.choose_spec.choose_spec.2.some.toHomeomorph') hu hv ⟨x,hxu⟩
    mem_chart_source := fun x ↦ by exact (hM.locally_modelled x).choose_spec.2.1
    chart_mem_atlas := fun x ↦ by
      let e := (hM.locally_modelled x).choose_spec.2.2.choose_spec.choose_spec.2.some
      dsimp; rw [PartialEquiv.fromEquivSourceTarget_toEquiv]
      exact ⟨e.dsmooth,e.symm.dsmooth⟩
  }
