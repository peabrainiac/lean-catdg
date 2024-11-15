import Orbifolds.Diffeology.LocallyModelled
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners


/-!
# Diffeological manifolds
Some lemmas and theorems on manifolds as diffeological spaces, as defined in
`Orbifolds.Diffeology.LocallyModelled`. The main purpose of this file is to show how this
relates to the notion of smooth manifolds defined in mathlib , i.e. that those are indeed
equivalent.
-/

open Set

open scoped Manifold

open PartialHomeomorph in
/-- The diffeology defined by a manifold structure on M, with the plots given by the maps
  that are smooth in the sense of mathlib's `ContMDiff`-API.
  This can not be an instance because `SmoothManifoldWithCorners I M` depends on `I` while
  `DiffeologicalSpace M` does not, and because it would probably lead to instance diamonds on
  things like products even if some workaround was found. -/
def SmoothManifoldWithCorners.toDiffeology {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] :
    DiffeologicalSpace M where
  plots n := {p | Smooth (𝓡 n) I p}
  constant_plots := fun _ => smooth_const
  plot_reparam {n m p f} := fun hp hf => hp.comp hf.contMDiff.smooth
  locality {n p} := fun h x => by
    have ⟨u,hu,hxu,hu'⟩ := h x; let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 hu x hxu
    refine' ContMDiffWithinAt.contMDiffAt _ (Metric.ball_mem_nhds x hε)
    have h := @hu' n (unitBallBall x ε hε ∘ univUnitBall)
      (fun x' => hε' ((unitBallBall x ε hε).mapsTo (univUnitBall.mapsTo trivial)))
        ((contDiff_unitBallBall hε).comp contDiff_univUnitBall); rw [mem_setOf_eq] at h
    have h' := (contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm hε).contDiffOn
      (n := ⊤) ((unitBallBall x ε hε).symm_mapsTo.subset_preimage)).contMDiffOn
    refine' (h.contMDiff.comp_contMDiffOn h').congr (fun x' hx' => _) x (Metric.mem_ball_self hε)
    simp_rw [Function.comp_apply, univUnitBall.right_inv ((unitBallBall x ε hε).symm_mapsTo hx'),
      (unitBallBall x ε hε).right_inv hx']

/-- The plots of a manifold are by definition precisely the smooth maps. -/
lemma isPlot_iff_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M]
    {n : ℕ} {p : Eucl n → M} : IsPlot[m.toDiffeology] p ↔ Smooth (𝓡 n) I p := Iff.rfl

lemma SmoothManifoldWithCorners.toDiffeology_eq_euclideanDiffeology {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (model_space_smooth (I := 𝓘(ℝ,E))).toDiffeology = euclideanDiffeology := by
  ext n p; exact contMDiff_iff_contDiff

def ModelWithCorners.toHomeomorphTarget {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : H ≃ₜ I.target where
  toFun x := ⟨I x,I.map_source (I.source_eq ▸ mem_univ x)⟩
  invFun y := I.invFun y
  left_inv := I.left_inv
  right_inv := fun _ => Subtype.ext <| I.right_inv _

/-- The D-topology on a manifold is always at least as fine as the usual topology. -/
lemma SmoothManifoldWithCorners.dTop_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [tM : TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M] :
    DTop[m.toDiffeology] ≤ tM :=
  TopologicalSpace.le_def.2 fun _ hu _ _ hp => IsOpen.preimage (hp.continuous) hu

/-- If the subspace topology and D-topology agree on the set `H` that the manifold is modelled on,
  the topology of the manifold agrees with the D-topology as well.-/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [tH : TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [@DTopCompatible I.target _ <| @instDiffeologicalSpaceSubtype _ euclideanDiffeology _]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M] :
    let _ := m.toDiffeology; DTopCompatible M := let _ := m.toDiffeology; ⟨by
  let dE := euclideanDiffeology (X := E); let dH := dE.induced I
  have : DTopCompatible H := ⟨by
    dsimp [dH]; rw [show ↑I = (↑) ∘ I.toHomeomorphTarget by rfl,←dE.induced_compose,
      dTop_induced_comm (by convert isOpen_univ; exact Equiv.range_eq_univ _),dTop_eq _,
      Homeomorph.induced_eq]⟩
  ext u; refine' ⟨fun h => _,fun hu n p hp => IsOpen.preimage (hp.continuous) hu⟩
  refine' isOpen_iff_mem_nhds.2 fun x hxu => mem_nhds_iff.2
    ⟨_,inter_subset_right _ _,_,mem_chart_source H x,hxu⟩
  have _ := (chartAt H x).open_target.dTopCompatible
  refine' Subtype.image_preimage_val _ _ ▸ (chartAt H x).open_source.isOpenMap_subtype_val _ _
  rw [←(chartAt H x).toHomeomorphSourceTarget.symm.isOpen_preimage]
  simp_rw [←dTop_eq (chartAt H x).target]; rw [isOpen_iff_preimages_plots]; intro n p hp
  simp_rw [←preimage_comp,Function.comp.assoc]
  rw [isOpen_iff_preimages_plots] at h; refine' h n _ _; rw [isPlot_iff_smooth]
  replace hp := (isPlot_induced_iff.1 <| isPlot_induced_iff.1 hp).contMDiff.smooth
  replace hp := (contMDiffOn_model_symm).smoothOn.comp_smooth hp fun x => mem_range_self _
  rw [←Function.comp.assoc,I.symm_comp_self,Function.id_comp] at hp
  exact (contMDiffOn_chart_symm (x := x)).smoothOn.comp_smooth hp fun x => (p x).2⟩

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
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M] :
    let _ := m.toDiffeology; DTopCompatible M := by
  let _ := m.toDiffeology; let _ := euclideanDiffeology (X := E)
  have : DTopCompatible I.target :=
    I.target_eq.trans hI.range_eq_univ ▸ isOpen_univ.dTopCompatible
  infer_instance

/-- Every smooth map between manifolds is also D-smooth, i.e. this construction defines a
  functor of concrete categories. -/
theorem Smooth.dsmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [m' : SmoothManifoldWithCorners I' N]
    {f : M → N} (hf : Smooth I I' f) : DSmooth[m.toDiffeology,m'.toDiffeology] f :=
  fun _ _ => hf.comp

/-- Every map between manifolds that is smooth on a subset is also smooth diffeologically
  with respect to the subspace diffeology. -/
theorem SmoothOn.dsmooth_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [m' : SmoothManifoldWithCorners I' N]
    {f : M → N} {s : Set M} (hf : SmoothOn I I' f s) :
    let _ := m.toDiffeology; let _ := m'.toDiffeology; DSmooth (s.restrict f) := by
  let _ := m.toDiffeology; let _ := m'.toDiffeology
  refine' fun n p hp => _
  rw [restrict_eq,Function.comp.assoc]
  exact hf.comp_smooth hp fun x => (p x).2

open PartialHomeomorph in
/-- Every D-smooth map from a boundaryless manifold to another manifold is also smooth.
  This could probably be proven in quite a lot greater generality. -/
theorem IsOpen.dsmooth_iff_smoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M]
    [hI : I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} (N : Type*)
    [TopologicalSpace N] [ChartedSpace H' N] [m' : SmoothManifoldWithCorners I' N]
    {f : M → N} {s : Set M} (hs : IsOpen s) : let _ := m.toDiffeology;
    let _ := m'.toDiffeology; DSmooth (s.restrict f) ↔ SmoothOn I I' f s := by
  let _ := m.toDiffeology; let _ := m'.toDiffeology
  refine' ⟨fun hf x hxs => _,SmoothOn.dsmooth_restrict⟩
  -- TODO
  sorry

open PartialHomeomorph in
/-- Every D-smooth map from a boundaryless manifold to another manifold is also smooth.
  This could probably be proven in quite a lot greater generality. -/
theorem DSmooth.smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M]
    [hI : I.Boundaryless]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [m' : SmoothManifoldWithCorners I' N]
    {f : M → N} (hf : DSmooth[m.toDiffeology,m'.toDiffeology] f) : Smooth I I' f := by
  let _ := m.toDiffeology; let _ := m'.toDiffeology
  intro x; let x' := toEuclidean (extChartAt I x x); let n := FiniteDimensional.finrank ℝ E
  let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 (toEuclidean.isOpenMap _ (isOpen_extChartAt_target I x))
    x' <| mem_image_of_mem _ <| (extChartAt I x).map_source (mem_extChartAt_source I x)
  let e := (extChartAt I x).symm ∘ toEuclidean.symm ∘
    (univUnitBall.trans' (unitBallBall x' ε hε) rfl)
  have he : Smooth (𝓡 n) I e := (contMDiffOn_extChartAt_symm x).comp_contMDiff (ContDiff.contMDiff
    (toEuclidean.symm.contDiff.comp <| (contDiff_unitBallBall hε).comp contDiff_univUnitBall))
    fun x'' => (mem_image_equiv (f := toEuclidean.toEquiv)).1 <| hε' <| map_source _ <| mem_univ _
  let e' := (univUnitBall.trans' (unitBallBall x' ε hε) rfl).symm ∘ toEuclidean ∘ extChartAt I x
  have he' : SmoothOn I (𝓡 n) e' _ :=
    (contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm hε).contDiffOn fun _ hx'' =>
        mem_preimage.2 ((unitBallBall x' ε hε).symm.map_source hx'')).contMDiffOn.comp
      (toEuclidean.contDiff.contMDiff.comp_contMDiffOn <| contMDiffOn_extChartAt.mono <|
        inter_subset_right _ _) (inter_subset_left _ _)
  refine' (((hf n _ he).comp_smoothOn he').congr (fun x'' hx'' => _) x _).contMDiffAt _
  · simp_rw [e,e',Function.comp_apply]
    rw [(univUnitBall.trans' (unitBallBall x' ε hε) rfl).right_inv (by exact hx''.1),
      toEuclidean.symm_apply_apply,(extChartAt I x).left_inv (extChartAt_source I x ▸ hx''.2)]
  · exact ⟨Metric.mem_ball_self hε,mem_chart_source H x⟩
  · refine' IsOpen.mem_nhds _ ⟨Metric.mem_ball_self hε,mem_chart_source H x⟩
    exact inter_comm _ _ ▸ extChartAt_source I x ▸ ContinuousOn.isOpen_inter_preimage
      (toEuclidean.continuous.comp_continuousOn (continuousOn_extChartAt I x))
      (isOpen_extChartAt_source I x) Metric.isOpen_ball

/-- A finite-dimensional, boundaryless `SmoothManifoldWithCorners` is also a manifold in the
  diffeological sense of `IsManifold`. -/
theorem SmoothManifoldWithCorners.isManifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [m : SmoothManifoldWithCorners I M]
    [hI : I.Boundaryless] : @IsManifold (FiniteDimensional.finrank ℝ E) M m.toDiffeology :=
  let _ := m.toDiffeology; let _ := euclideanDiffeology (X := E)
  ⟨fun x => (dTop_eq M).symm ▸ ⟨_,isOpen_extChartAt_source I x,mem_extChartAt_source I x,
    (),_,toEuclidean.isOpenMap _ (isOpen_extChartAt_target I x),⟨{
      toEquiv := ((extChartAt I x).trans' (toEuclidean.toEquiv.toPartialEquivOfImageEq
        (extChartAt I x).target _ rfl) rfl).toEquiv
      dsmooth_toFun := by
        dsimp [PartialEquiv.trans',PartialEquiv.toEquiv,-extChartAt]
        refine' (toEuclidean.contDiff.dsmooth.comp _).subtype_mk _
        exact (toDiffeology_eq_euclideanDiffeology (E := E) ▸ (extChartAt_source I x).symm ▸
          (contMDiffOn_extChartAt (I := I) (x := x)).smoothOn.dsmooth_restrict:)
      dsmooth_invFun := by
        dsimp [PartialEquiv.trans',PartialEquiv.toEquiv,-extChartAt]
        refine' DSmooth.subtype_mk _ _
        rw [←Function.comp_def (extChartAt I x).symm,←Function.comp_def _ Subtype.val,
          ←(mapsTo_image _ _).restrict_commutes _ _ _,←Function.comp.assoc]
        refine' DSmooth.comp _ (toEuclidean.symm.contDiff.dsmooth.restrict _)
        exact (toEuclidean.symm_image_image (extChartAt I x).target).symm ▸
          (toDiffeology_eq_euclideanDiffeology (E := E) ▸
            (contMDiffOn_extChartAt_symm (I := I) x).smoothOn.dsmooth_restrict:)
    }⟩⟩⟩

-- TODO: move this and related lemmas to a more fitting place
open Classical in
@[simps]
noncomputable def PartialEquiv.fromEquivSourceTarget {α β : Type*} {s : Set α} {t : Set β}
    (e : s ≃ t) (a : s) : PartialEquiv α β where
  toFun := fun x => if hx : x ∈ s then e ⟨x,hx⟩ else e a
  invFun := fun y => if hy : y ∈ t then e.symm ⟨y,hy⟩ else a
  source := s
  target := t
  map_source' := fun _ hx => by simp [hx]
  map_target' := fun _ hy => by simp [hy]
  left_inv' := fun _ hx => by simp [hx]
  right_inv' := fun _ hy => by simp [hy]

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
noncomputable def PartialHomeomorph.fromHomeomorphSourceTarget {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {s : Set α} {t : Set β} (e : s ≃ₜ t) (hs : IsOpen s) (ht : IsOpen t)
    (a : s) : PartialHomeomorph α β where
  toPartialEquiv := PartialEquiv.fromEquivSourceTarget e.toEquiv a
  open_source := hs
  open_target := ht
  continuousOn_toFun := by simp [continuousOn_iff_continuous_restrict,continuous_subtype_val]
  continuousOn_invFun := by simp [continuousOn_iff_continuous_restrict,continuous_subtype_val]

@[simp]
lemma PartialHomeomorph.fromHomeomorphSourceTarget_toPartialEquiv {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {t : Set β} (e : s ≃ₜ t) (hs : IsOpen s)
    (ht : IsOpen t) (a : s) : (fromHomeomorphSourceTarget e hs ht a).toPartialEquiv =
    PartialEquiv.fromEquivSourceTarget e.toEquiv a := rfl

/-- Charted space structure of a diffeological manifold, consisting of all local diffeomorphisms
  between `M` and `Eucl n`. -/
noncomputable def IsManifold.toChartedSpace {M : Type*} [DiffeologicalSpace M] {n : ℕ}
    [hM : IsManifold n M] : @ChartedSpace (Eucl n) _ M DTop := by
  let _ := @DTop M _; let _ : DTopCompatible M := ⟨rfl⟩; exact {
    atlas := {e | DSmooth e.toEquiv ∧ DSmooth e.toEquiv.symm}
    chartAt := fun x => by
      have h := hM.locally_modelled x
      have hu := h.choose_spec.1; have hxu := h.choose_spec.2.1
      have hv := h.choose_spec.2.2.choose_spec.choose_spec.1
      have _ := hu.dTopCompatible; have _ := hv.dTopCompatible
      exact PartialHomeomorph.fromHomeomorphSourceTarget
        (h.choose_spec.2.2.choose_spec.choose_spec.2.some.toHomeomorph') hu hv ⟨x,hxu⟩
    mem_chart_source := fun x => by exact (hM.locally_modelled x).choose_spec.2.1
    chart_mem_atlas := fun x => by
      let e := (hM.locally_modelled x).choose_spec.2.2.choose_spec.choose_spec.2.some
      dsimp; rw [PartialEquiv.fromEquivSourceTarget_toEquiv]
      exact ⟨e.dsmooth,e.symm.dsmooth⟩
  }
