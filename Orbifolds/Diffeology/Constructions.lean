import Orbifolds.Diffeology.Maps
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open TopologicalSpace Set

open Topology

section Constructions

instance instDiffeologicalSpaceSubtype {X : Type*} [DiffeologicalSpace X] {p : X → Prop} :
    DiffeologicalSpace (Subtype p) :=
  DiffeologicalSpace.induced ((↑) : _ → X) inferInstance

instance Pi.diffeologicalSpace {ι : Type*} {Y : ι → Type*}
    [(i : ι) → DiffeologicalSpace (Y i)] : DiffeologicalSpace ((i : ι) → Y i) where
  plots n := {p | ∀ i, IsPlot ((fun y => y i) ∘ p)}
  constant_plots _ i := isPlot_const
  plot_reparam {n m p f} := fun hp hf i => by
    exact Function.comp.assoc _ _ _ ▸ isPlot_reparam (hp i) hf

end Constructions

section Pi

variable {ι : Type*} {Y : ι → Type*} [(i : ι) → DiffeologicalSpace (Y i)]
  {X : Type*} [DiffeologicalSpace X] {f : X → ((i : ι) → Y i)}

theorem dsmooth_pi_iff : DSmooth f ↔ ∀ i, DSmooth fun x => f x i := by
  simp only [dsmooth_def,@forall_comm ι _ _]; rfl

@[fun_prop]
theorem dsmooth_pi (h : ∀ i, DSmooth fun a => f a i) : DSmooth f :=
  dsmooth_pi_iff.2 h

@[fun_prop]
theorem dsmooth_apply (i : ι) : DSmooth fun p : (i : ι) → Y i => p i :=
  dsmooth_pi_iff.1 dsmooth_id i

-- TODO. something like this should be true, but I haven't yet figured out the exact details.
instance [Fintype ι] [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → LocallyCompactSpace (Y i)]
    [(i : ι) → DTopCompatible (Y i)] : DTopCompatible ((i : ι) → Y i) := ⟨by
  ext s; rw [isOpen_pi_iff',isOpen_iff_preimages_plots]
  refine' ⟨fun h => _, fun h n p hp => _⟩
  all_goals sorry⟩

instance {ι : Type*} [Fintype ι] {Y : ι → Type*} [(i : ι) → NormedAddCommGroup (Y i)]
    [(i : ι) → NormedSpace ℝ (Y i)] [(i : ι) → DiffeologicalSpace (Y i)]
    [(i : ι) → ContDiffCompatible (Y i)] : ContDiffCompatible ((i : ι) → Y i) :=
  ⟨by simp_rw [contDiff_pi,←ContDiffCompatible.isPlot_iff]; rfl⟩

end Pi

section Subtype

variable {X : Type*} [DiffeologicalSpace X] {s : Set X} {p : X → Prop}
  {Y : Type*} [DiffeologicalSpace Y]

theorem induction_subtype_val : Induction ((↑) : s → X) :=
  ⟨Subtype.coe_injective,rfl⟩

theorem Induction.of_codRestrict {f : X → Y} {t : Set Y} (ht : ∀ x, f x ∈ t)
    (h : Induction (t.codRestrict f ht)) : Induction f :=
  by sorry

theorem dsmooth_subtype_val : DSmooth ((↑) : s → X) :=
  induction_subtype_val.dsmooth

theorem DSmooth.subtype_val {f : Y → Subtype p} (hf : DSmooth f) :
    DSmooth fun x => (f x : X) :=
  dsmooth_subtype_val.comp hf

theorem DSmooth.subtype_mk {f : Y → X} (hf : DSmooth f) (hp : ∀ x, p (f x)) :
    DSmooth fun x => (⟨f x, hp x⟩ : Subtype p) :=
  hf

theorem DSmooth.subtype_map {f : X → Y} (h : DSmooth f) {q : Y → Prop}
    (hpq : ∀ x, p x → q (f x)) : DSmooth (Subtype.map f hpq) :=
  (h.comp dsmooth_subtype_val).subtype_mk _

theorem dsmooth_inclusion {s t : Set X} (h : s ⊆ t) : DSmooth (inclusion h) :=
  dsmooth_id.subtype_map h

theorem DSmooth.codRestrict {f : X → Y} {s : Set Y} (hf : DSmooth f) (hs : ∀ a, f a ∈ s) :
    DSmooth (s.codRestrict f hs) :=
  hf.subtype_mk hs

theorem DSmooth.restrict {f : X → Y} {s : Set X} {t : Set Y} (h1 : MapsTo f s t)
    (h2 : DSmooth f) : DSmooth (h1.restrict f s t) :=
  (h2.comp dsmooth_subtype_val).codRestrict _

theorem DSmooth.restrictPreimage {f : X → Y} {s : Set Y} (h : DSmooth f) :
    DSmooth (s.restrictPreimage f) :=
  h.restrict _

theorem Induction.codRestrict {f : X → Y} (hf : Induction f) {s : Set Y} (hs : ∀ x, f x ∈ s) :
    Induction (s.codRestrict f hs) :=
  by sorry

/-- TODO: move to Mathlib.Topology.Constructions -/
theorem IsOpenMap.subtype_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {f : Y → X} (hf : IsOpenMap f) (hfs : ∀ x, f x ∈ s) :
    IsOpenMap fun x => (⟨f x, hfs x⟩ : Subtype s) := fun u hu => by
  convert (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun x => exists_congr fun x' => and_congr_right' Subtype.ext_iff

/-- TODO: move to Mathlib.Topology.Constructions -/
theorem IsOpen.isOpenMap_subtype_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} {f : X → Y} (hs : IsOpen s) (hf : IsOpenMap f)
    (hst : ∀ x, s x → t (f x)) : IsOpenMap (Subtype.map f hst) :=
  (hf.comp hs.isOpenMap_subtype_val).subtype_mk _

/-- TODO: move to Mathlib.Topology.Constructions -/
theorem IsOpen.isOpenMap_inclusion {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (h : s ⊆ t) : IsOpenMap (inclusion h) :=
  hs.isOpenMap_subtype_map IsOpenMap.id h

/-- TODO: move to Mathlib.Topology.Constructions -/
theorem IsOpenMap.codRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} (hf : IsOpenMap f) (hs : ∀ a, f a ∈ s) :
    IsOpenMap (s.codRestrict f hs) :=
  hf.subtype_mk hs

/-- The D-topology is also characterised by the smooth maps `u → X` for open `u`. -/
lemma isOpen_iff_preimages_plots' {s : Set X} : IsOpen[DTop] s ↔
    ∀ (n : ℕ) (u : Set (Eucl n)) (p : u → X), IsOpen u → DSmooth p → IsOpen (p ⁻¹' s) := by
  rw [isOpen_iff_preimages_plots]
  refine' ⟨fun hs n u p hu hp => _,fun hs n p hp => _⟩
  · refine' isOpen_iff_mem_nhds.2 fun x hx => _
    let ⟨ε,hε⟩ := Metric.isOpen_iff.1 hu x x.2
    let e : Eucl n ≃ₜ Metric.ball x.1 ε := (Homeomorph.Set.univ _).symm.trans <|
      PartialHomeomorph.univUnitBall.toHomeomorphSourceTarget.trans
        (PartialHomeomorph.unitBallBall x.1 ε hε.1).toHomeomorphSourceTarget
    have he : DSmooth e :=
      (((PartialHomeomorph.contDiff_unitBallBall hε.1).dsmooth.restrict
        (PartialHomeomorph.unitBallBall x.1 ε hε.1).map_source').comp
          (PartialHomeomorph.contDiff_univUnitBall.dsmooth.restrict
            PartialHomeomorph.univUnitBall.map_source')).comp (dsmooth_id.subtype_mk _)
    have h := hs n _ (hp.comp ((dsmooth_inclusion hε.2).comp he)).isPlot
    simp_rw [preimage_comp, Homeomorph.isOpen_preimage] at h
    apply Metric.isOpen_ball.isOpenMap_inclusion hε.2 _ at h
    rw [image_preimage_eq_inter_range] at h
    exact mem_nhds_iff.2 ⟨_,inter_subset_left _ _,h,hx,by simp [hε.1]⟩
  · let e := Homeomorph.Set.univ (Fin n → ℝ)
    rw [←e.isOpen_preimage,←preimage_comp]
    exact hs n _ (p ∘ e) isOpen_univ (hp.dsmooth.comp dsmooth_subtype_val)

/-- On open subsets, the D-topology and subspace topology agree. -/
protected theorem IsOpen.dTopCompatible [TopologicalSpace X] [DTopCompatible X] (hs : IsOpen s) :
    DTopCompatible s := ⟨by
  ext t; refine' ⟨fun ht => _,fun ht => _⟩
  all_goals rw [←Subtype.val_injective.preimage_image t]
  · refine' IsOpen.preimage continuous_subtype_val (dTop_eq X ▸ _)
    refine' isOpen_iff_preimages_plots.2 fun n p hp => _
    have hs' := hs.preimage hp.dsmooth.continuous'
    convert hs'.isOpenMap_subtype_val _ <| ((isOpen_iff_preimages_plots' (s := t)).1 ht) n _
      (s.restrictPreimage p) hs' hp.dsmooth.restrictPreimage
    ext x; simp_rw [mem_preimage, mem_image, Subtype.exists, exists_and_right, exists_eq_right]; rfl
  · refine' @IsOpen.preimage s X DTop _ _ _ _ (hs.isOpenMap_subtype_val t ht)
    exact dTop_eq X ▸ dsmooth_subtype_val.continuous⟩

end Subtype
