import Orbifolds.Diffeology.Maps
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open TopologicalSpace Set

open Topology

section Constructions

instance instDiffeologicalSpaceSubtype {X : Type*} [DiffeologicalSpace X] {p : X → Prop} :
    DiffeologicalSpace (Subtype p) :=
  DiffeologicalSpace.induced ((↑) : _ → X) inferInstance

-- `Pi.diffeologicalSpace` is currently already defined in `Orbifolds.Diffeology.Basic`.

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

/-- The D-topology is also characterised by the smooth maps `u → X` for open `u`.
TODO: this is probably easier using `EuclideanSpace ℝ (Fin n)` as the test spaces instead of
`Fin n → ℝ`, since the proof uses `PartialHomeomorph.contDiff_univBall` which works
only in inner product spaces. Since I've been thinking about switching to
`EuclideanSpace ℝ (Fin n)` anyways, I've decided to wait with this until then. -/
lemma isOpen_iff_preimages_plots' {s : Set X} : IsOpen[DTop] s ↔
    ∀ (n : ℕ) (u : Set (Fin n → ℝ)) (p : u → X), IsOpen u → DSmooth p → IsOpen (p ⁻¹' s) := by
  rw [isOpen_iff_preimages_plots]
  refine' ⟨fun hs n u p hu hp => _,fun hs n p hp => _⟩
  · refine' isOpen_iff_mem_nhds.2 fun x hx => _
    let ⟨ε,hε⟩ := Metric.isOpen_iff.1 hu x x.2
    let e' : (Fin n → ℝ) ≃ₜ _ := (EuclideanSpace.equiv _ _).toHomeomorph.symm.trans <|
      (Homeomorph.Set.univ _).symm.trans <|
        (PartialHomeomorph.univBall_source (P := EuclideanSpace ℝ (Fin n)) _ _ ▸
          (PartialHomeomorph.univBall_target (P := EuclideanSpace ℝ (Fin n)) _ hε.1 ▸
            (PartialHomeomorph.univBall (P := EuclideanSpace ℝ (Fin n)) x.1 ε).toHomeomorphSourceTarget))
    have he' : DSmooth e' := by
      simp [e',Homeomorph.trans]
      refine' DSmooth.comp _ (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.dsmooth
      refine' DSmooth.comp _ (DSmooth.subtype_mk dsmooth_id _)
      have h := (PartialHomeomorph.contDiff_univBall (n := ⊤) (E := EuclideanSpace ℝ (Fin n))
        (c := x.1) (r := ε)).dsmooth
      have h' := h.restrict (show MapsTo (β := EuclideanSpace _ _) _ univ (Metric.ball x.1 ε) by
        sorry)
      sorry
    --have := hs n (p ∘ inclusion hε.2 ∘ e) (hp.comp ((dsmooth_inclusion hε.2).comp he)).isPlot
    sorry
  · let e := Homeomorph.Set.univ (Fin n → ℝ)
    rw [←e.isOpen_preimage,←preimage_comp]
    exact hs n _ (p ∘ e) isOpen_univ (hp.dsmooth.comp dsmooth_subtype_val)

/-- On open subsets, the D-topology and subspace toplogy agree. -/
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
