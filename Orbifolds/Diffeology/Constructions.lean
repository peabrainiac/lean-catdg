import Orbifolds.Diffeology.DSmoothMap
import Orbifolds.ForMathlib.DeltaGeneratedSpace
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Constructions of diffeological spaces
This file gives some concrete constructions like products and coproducts of
diffeological spaces. General limits and colimits are found in
`Orbifolds.Diffeology.DiffCat`.

Mostly based on `Mathlib.Topology.Constructions`.
-/

set_option autoImplicit false

open TopologicalSpace Set

open Topology

universe u v

section Constructions

instance instDiffeologicalSpaceSubtype {X : Type*} [DiffeologicalSpace X] {p : X → Prop} :
    DiffeologicalSpace (Subtype p) :=
  DiffeologicalSpace.induced ((↑) : _ → X) inferInstance

instance {X : Type*} {r : X → X → Prop} [d : DiffeologicalSpace X] :
    DiffeologicalSpace (Quot r) :=
  d.coinduced (Quot.mk r)

instance instDiffeologicalSpaceQuotient {X : Type*} {s : Setoid X} [d : DiffeologicalSpace X] :
    DiffeologicalSpace (Quotient s) :=
  d.coinduced Quotient.mk'

instance instDiffeologicalSpaceProd {X Y : Type*} [dX : DiffeologicalSpace X]
    [dY : DiffeologicalSpace Y] : DiffeologicalSpace (X × Y) :=
  dX.induced Prod.fst ⊓ dY.induced Prod.snd

instance Pi.diffeologicalSpace {ι : Type*} {Y : ι → Type*}
    [D : (i : ι) → DiffeologicalSpace (Y i)] : DiffeologicalSpace ((i : ι) → Y i) :=
  ⨅ i : ι, (D i).induced (fun x => x i)

instance ULift.diffeologicalSpace {X : Type u} [t : DiffeologicalSpace X] :
    DiffeologicalSpace (ULift.{v, u} X) :=
  t.induced ULift.down

end Constructions

/-!
### `Additive`, `Multiplicative`

The diffeology on those type synonyms is inherited without change.
-/

section

variable {X : Type*} [DiffeologicalSpace X]

open Additive Multiplicative

instance : DiffeologicalSpace (Additive X) := ‹DiffeologicalSpace X›

instance : DiffeologicalSpace (Multiplicative X) := ‹DiffeologicalSpace X›

-- TODO: discrete diffeology instance, once that is available as a typeclass

theorem dsmooth_ofMul : DSmooth (ofMul : X → Additive X) := dsmooth_id

theorem dsmooth_toMul : DSmooth (toMul : Additive X → X) := dsmooth_id

theorem dsmooth_ofAdd : DSmooth (ofAdd : X → Multiplicative X) := dsmooth_id

theorem dsmooth_toAdd : DSmooth (toAdd : Multiplicative X → X) := dsmooth_id

theorem induction_ofMul : Induction (ofMul : X → Additive X) := induction_id

theorem induction_toMul : Induction (toMul : Additive X → X) := induction_id

theorem induction_ofAdd : Induction (ofAdd : X → Multiplicative X) := induction_id

theorem induction_toAdd : Induction (toAdd : Multiplicative X → X) := induction_id

theorem subduction_ofMul : Subduction (ofMul : X → Additive X) := subduction_id

theorem subduction_toMul : Subduction (toMul : Additive X → X) := subduction_id

theorem subduction_ofAdd : Subduction (ofAdd : X → Multiplicative X) := subduction_id

theorem subduction_toAdd : Subduction (toAdd : Multiplicative X → X) := subduction_id

end

/-!
### Order dual

The diffeology on this type synonym is inherited without change.
-/

section OrderDual

variable {X : Type*} [DiffeologicalSpace X]

open OrderDual

instance : DiffeologicalSpace Xᵒᵈ := ‹DiffeologicalSpace X›

theorem dsmooth_toDual : DSmooth (toDual : X → Xᵒᵈ) := dsmooth_id

theorem dsmooth_ofDual : DSmooth (ofDual : Xᵒᵈ → X) := dsmooth_id

theorem induction_toDual : Induction (toDual : X → Xᵒᵈ) := induction_id

theorem induction_ofDual : Induction (ofDual : Xᵒᵈ → X) := induction_id

theorem subduction_toDual : Subduction (toDual : X → Xᵒᵈ) := subduction_id

theorem subduction_ofDual : Subduction (ofDual : Xᵒᵈ → X) := subduction_id

end OrderDual

section Pi

variable {ι : Type*} {Y : ι → Type*} [(i : ι) → DiffeologicalSpace (Y i)]
  {X : Type*} [DiffeologicalSpace X] {f : X → ((i : ι) → Y i)}

theorem dsmooth_pi_iff : DSmooth f ↔ ∀ i, DSmooth fun x => f x i := by
  simp_rw [dsmooth_iff_coinduced_le,Pi.diffeologicalSpace,le_iInf_iff]
  refine' forall_congr' fun i => _
  rw [←DiffeologicalSpace.coinduced_le_iff_le_induced,DiffeologicalSpace.coinduced_compose]; rfl

@[fun_prop]
theorem dsmooth_pi (h : ∀ i, DSmooth fun a => f a i) : DSmooth f :=
  dsmooth_pi_iff.2 h

@[fun_prop]
theorem dsmooth_apply (i : ι) : DSmooth fun p : (i : ι) → Y i => p i :=
  dsmooth_pi_iff.1 dsmooth_id i

theorem isPlot_pi_iff {n} {p : Eucl n → ((i : ι) → Y i)} :
    IsPlot p ↔ ∀ i, IsPlot fun x => p x i := by
  simp_rw [isPlot_iff_dsmooth,dsmooth_pi_iff]

-- TODO. something like this should be true, but I haven't yet figured out the exact details.
instance [Fintype ι] [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → LocallyCompactSpace (Y i)]
    [(i : ι) → DTopCompatible (Y i)] : DTopCompatible ((i : ι) → Y i) := ⟨by
  ext s; rw [isOpen_pi_iff',isOpen_iff_preimages_plots]
  refine' ⟨fun h => _, fun h n p hp => _⟩
  all_goals sorry⟩

instance {ι : Type*} [Fintype ι] {Y : ι → Type*} [(i : ι) → NormedAddCommGroup (Y i)]
    [(i : ι) → NormedSpace ℝ (Y i)] [(i : ι) → DiffeologicalSpace (Y i)]
    [(i : ι) → ContDiffCompatible (Y i)] : ContDiffCompatible ((i : ι) → Y i) :=
  ⟨fun {_ _} => by simp_rw [contDiff_pi,←ContDiffCompatible.isPlot_iff,isPlot_pi_iff]⟩

end Pi

section Subtype

variable {X : Type*} [DiffeologicalSpace X] {s : Set X} {p : X → Prop}
  {Y : Type*} [DiffeologicalSpace Y]

theorem induction_subtype_val : Induction ((↑) : s → X) :=
  ⟨Subtype.coe_injective,rfl⟩

theorem Induction.of_codRestrict {f : X → Y} {t : Set Y} (ht : ∀ x, f x ∈ t)
    (hf : Induction (t.codRestrict f ht)) : Induction f :=
  induction_subtype_val.comp hf

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
  Induction.of_comp' (hf.dsmooth.codRestrict hs) dsmooth_subtype_val hf

-- TODO: move to mathlib.
theorem ContDiffOn.comp_contDiff {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞} {s : Set F} {f : E → F} {g : F → G}
    (hg : ContDiffOn 𝕜 n g s) (hf : ContDiff 𝕜 n f) (hs : ∀ x, f x ∈ s) :
    ContDiff 𝕜 n (g ∘ f) :=
  contDiffOn_univ.1 <| hg.comp (contDiffOn_univ.2 hf) fun x _ => hs x

theorem ContDiffOn.dsmooth_restrict [NormedAddCommGroup X] [NormedSpace ℝ X] [ContDiffCompatible X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [ContDiffCompatible Y]
    {f : X → Y} (hf : ContDiffOn ℝ ⊤ f s) : DSmooth (s.restrict f) := by
  refine' fun n p hp => isPlot_iff_contDiff.2 _
  rw [restrict_eq,Function.comp.assoc]
  exact hf.comp_contDiff (isPlot_iff_contDiff.1 hp) fun x => (p x).2

-- TODO: relax dimensionality hypothesis?
open PartialHomeomorph in
/-- On an open subset, a function is smooth in the usual sense iff it is smooth diffeologically. -/
theorem IsOpen.dsmooth_iff_contDiffOn [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [ContDiffCompatible X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [ContDiffCompatible Y]
    {f : X → Y} (hs : IsOpen s) : DSmooth (s.restrict f) ↔ ContDiffOn ℝ ⊤ f s := by
  refine' ⟨fun hf x hxs => _,ContDiffOn.dsmooth_restrict⟩
  let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 hs x hxs
  refine' ContDiffWithinAt.mono_of_mem (s := Metric.ball x ε) _ <| mem_nhdsWithin.2
    ⟨_,Metric.isOpen_ball,Metric.mem_ball_self hε,inter_subset_left _ _⟩
  suffices h : ContDiffOn ℝ ⊤ f (Metric.ball x ε) by exact h x (Metric.mem_ball_self hε)
  let e := univUnitBall.trans' (unitBallBall x ε hε) rfl
  have he : DSmooth e :=
    (contDiff_unitBallBall hε).dsmooth.comp contDiff_univUnitBall.dsmooth
  let hes x : e x ∈ s := hε' (e.map_source (mem_univ x))
  refine' ContDiffOn.congr (f := (f ∘ e) ∘ e.symm) _ fun x hx => by
    rw [Function.comp_apply]; exact congrArg _ (e.right_inv' hx).symm
  refine' ContDiff.comp_contDiffOn (DSmooth.contDiff _) _
  · rw [←restrict_comp_codRestrict (b := s) hes]
    exact hf.comp (DSmooth.codRestrict he hes)
  · exact contDiffOn_univUnitBall_symm.comp (contDiff_unitBallBall_symm hε).contDiffOn
      (fun _ => (unitBallBall x ε hε).symm.map_source)

-- TODO: move to Mathlib.Topology.Constructions
theorem IsOpenMap.subtype_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {f : Y → X} (hf : IsOpenMap f) (hfs : ∀ x, f x ∈ s) :
    IsOpenMap fun x => (⟨f x, hfs x⟩ : Subtype s) := fun u hu => by
  convert (hf u hu).preimage continuous_subtype_val
  exact Set.ext fun x => exists_congr fun x' => and_congr_right' Subtype.ext_iff

-- TODO: move to Mathlib.Topology.Constructions
theorem IsOpen.isOpenMap_subtype_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} {f : X → Y} (hs : IsOpen s) (hf : IsOpenMap f)
    (hst : ∀ x, s x → t (f x)) : IsOpenMap (Subtype.map f hst) :=
  (hf.comp hs.isOpenMap_subtype_val).subtype_mk _

-- TODO: move to Mathlib.Topology.Constructions
theorem IsOpen.isOpenMap_inclusion {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsOpen s) (h : s ⊆ t) : IsOpenMap (inclusion h) :=
  hs.isOpenMap_subtype_map IsOpenMap.id h

-- TODO: move to Mathlib.Topology.Constructions
theorem IsOpenMap.codRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s : Set Y} (hf : IsOpenMap f) (hs : ∀ a, f a ∈ s) :
    IsOpenMap (s.codRestrict f hs) :=
  hf.subtype_mk hs

/-- The D-topology is also characterised by the smooth maps `u → X` for open `u`. -/
lemma isOpen_iff_preimages_plots' {s : Set X} : IsOpen[DTop] s ↔
    ∀ (n : ℕ) (u : Set (Eucl n)) (p : u → X), IsOpen u → DSmooth p → IsOpen (p ⁻¹' s) := by
  rw [isOpen_iff_preimages_plots]
  refine' ⟨fun hs n u p hu hp => _,fun hs n p hp => _⟩
  · rw [←isOpen_iff_preimages_plots] at hs
    have := dTop_induced_comm ((Subtype.range_val (s := u)).symm ▸ hu)
    convert @IsOpen.preimage _ _ DTop DTop p hp.continuous _ hs
    exact (dTop_induced_comm ((Subtype.range_val (s := u)).symm ▸ hu)).symm
  · let e := Homeomorph.Set.univ (Fin n → ℝ)
    rw [←e.isOpen_preimage,←preimage_comp]
    exact hs n _ (p ∘ e) isOpen_univ (hp.dsmooth.comp dsmooth_subtype_val)

/-- On open subsets, the D-topology and subspace topology agree. -/
protected theorem IsOpen.dTopCompatible [TopologicalSpace X] [DTopCompatible X] (hs : IsOpen s) :
    DTopCompatible s := ⟨by
  exact (dTop_eq X) ▸ dTop_induced_comm (Subtype.range_coe.symm ▸ (dTop_eq X) ▸ hs)⟩

instance [TopologicalSpace X] [DTopCompatible X] [h : Fact (IsOpen s)] : DTopCompatible s :=
  h.out.dTopCompatible

/-- Smoothness can also be characterised as preserving smooth maps `u → X` for open `u`.-/
theorem dsmooth_iff' {f : X → Y} : DSmooth f ↔
    ∀ (n : ℕ) (u : Set (Eucl n)) (p : u → X), IsOpen u → DSmooth p → DSmooth (f ∘ p) := by
  refine' ⟨fun hf n u p _ hp => hf.comp hp,fun hf n p hp => _⟩
  rw [←Function.comp_id (f ∘ p),←(Homeomorph.Set.univ _).self_comp_symm,←Function.comp.assoc]
  exact ((hf n _ _ isOpen_univ (hp.dsmooth.comp dsmooth_subtype_val)).comp
    (dsmooth_id.subtype_mk _)).isPlot

/-- The locality axiom of diffeologies. Restated here in terms of subspace diffeologies. -/
theorem isPlot_iff_locally_dsmooth {n : ℕ} {p : Eucl n → X} : IsPlot p ↔
    ∀ x : Eucl n, ∃ u, IsOpen u ∧ x ∈ u ∧  DSmooth (u.restrict p) := by
  refine' ⟨fun hp x => ⟨_,isOpen_univ,mem_univ x,hp.dsmooth.comp dsmooth_subtype_val⟩,_⟩
  refine' fun h => DiffeologicalSpace.locality fun x => _
  let ⟨u,hu,hxu,hu'⟩ := h x
  refine' ⟨u,hu,hxu,fun {m f} hfu hf => u.restrict_comp_codRestrict hfu ▸ _⟩
  exact  (hu' _ _ (hf.dsmooth.codRestrict hfu).isPlot)

theorem dsmooth_iff_locally_dsmooth {f : X → Y} : DSmooth f ↔
    ∀ x : X, ∃ u : Set X, IsOpen[DTop] u ∧ x ∈ u ∧ DSmooth (u.restrict f) := by
  refine' ⟨fun hf x => ⟨_,by simp,mem_univ x,hf.comp dsmooth_subtype_val⟩,fun h n p hp => _⟩
  refine' isPlot_iff_locally_dsmooth.2  fun x => _
  let ⟨u,hu,hxu,hu'⟩ := h (p x)
  refine' ⟨p ⁻¹' u,@IsOpen.preimage _ _ _ DTop p (dTop_eq (Eucl n) ▸ hp.continuous) u hu,hxu,_⟩
  exact hu'.comp hp.dsmooth.restrictPreimage

/-- Any D-locally constant map is smooth. -/
theorem IsLocallyConstant.dsmooth {f : X → Y} (hf : @IsLocallyConstant _ _ DTop f) :
    DSmooth f := by
  refine' dsmooth_iff_locally_dsmooth.2 fun x => Exists.imp (fun u ⟨hu,hxu,hu'⟩ => ⟨hu,hxu,_⟩)
    (@IsLocallyConstant.exists_open _ _ DTop f hf x)
  rw [show u.restrict f = fun _ => f x by ext x'; exact hu' x'.1 x'.2]
  exact dsmooth_const

end Subtype

section DTop

/-- The indiscrete diffeology is the one for which every map is a plot. -/
theorem DiffeologicalSpace.eq_top_iff {X : Type*} {dX : DiffeologicalSpace X} :
    dX = ⊤ ↔ ∀ n (p : Eucl n → X), IsPlot p :=
  ⟨fun h _ _ => h ▸ trivial,fun h => IsTop.eq_top fun _ => le_iff'.2 fun n p _ => h n p⟩

open PartialHomeomorph in
/-- The discrete diffeology is the one with only the constant maps as plots. -/
theorem DiffeologicalSpace.eq_bot_iff {X : Type*} {dX : DiffeologicalSpace X} :
    dX = ⊥ ↔ ∀ n (p : Eucl n → X), IsPlot p → ∃ x, p = fun _ => x := by
  refine' ⟨fun h n p => fun hp => _,fun h => IsBot.eq_bot fun d => _⟩
  · let d : DiffeologicalSpace X := {
      plots := fun n => {p | ∃ x, p = fun _ => x}
      constant_plots := fun x => ⟨x,rfl⟩
      plot_reparam := fun ⟨x,hx⟩ _ => ⟨x,by rw [hx]; rfl⟩
      locality := fun {n p} h => by
        have := Nonempty.map p inferInstance
        refine' IsLocallyConstant.exists_eq_const <| (IsLocallyConstant.iff_exists_open p).2 _
        intro x; let ⟨u,hu,hxu,hu'⟩ := h x; let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 hu x hxu
        refine' ⟨Metric.ball x ε,Metric.isOpen_ball,Metric.mem_ball_self hε,_⟩
        let e : Eucl n ≃ₜ Metric.ball x ε := (Homeomorph.Set.univ _).symm.trans <|
          univUnitBall.toHomeomorphSourceTarget.trans
            (unitBallBall x ε hε).toHomeomorphSourceTarget
        have he : DSmooth (((↑) : _ → Eucl n) ∘ e) :=
          (contDiff_unitBallBall hε).dsmooth.comp contDiff_univUnitBall.dsmooth
        let ⟨x'',hx''⟩ := @hu' n ((↑) ∘ e) (fun x'' => hε' (e x'').2) he.contDiff
        suffices h : ∀ x' : Metric.ball x ε, p x' = x'' by
          intro x' hx'; rw [h ⟨x',hx'⟩,h ⟨x,Metric.mem_ball_self hε⟩]
        intro x'
        rw [←Function.comp_apply (f := p),←Function.comp_id (p ∘ _),←e.self_comp_symm,
          ←Function.comp.assoc,Function.comp.assoc p,hx'',Function.comp_apply]}
    exact le_iff'.1 (h.symm ▸ bot_le (a := d)) n p hp
  · exact le_iff'.2 fun n p hp => (h n p hp).choose_spec ▸ isPlot_const

theorem dTop_mono {X : Type*} {d₁ d₂ : DiffeologicalSpace X} (h : d₁ ≤ d₂) :
    DTop[d₁] ≤ DTop[d₂] := by
  refine' TopologicalSpace.le_def.2 fun u hu => _
  rw [@isOpen_iff_preimages_plots] at hu ⊢
  rw [DiffeologicalSpace.le_iff'] at h
  exact fun n p => hu n p ∘ h n p

/-- The D-topology of the indiscrete diffeology is indiscrete. -/
theorem dTop_top {X : Type*} : DTop[⊤] = (⊤ : TopologicalSpace X) := by
  let f : X → Unit := default
  have h : @DTop Unit ⊤ = ⊥ := Unique.eq_default _
  rw [←DiffeologicalSpace.induced_top (f := f), dTop_induced_comm (by rw [h]; trivial),
    h.trans (Unique.default_eq ⊤),induced_top]

/-- The D-topology of the discrete diffeology is discrete. -/
theorem dTop_bot {X : Type*} : DTop[⊥] = (⊥ : TopologicalSpace X) := by
  ext u; refine' ⟨fun _ => trivial,fun _ => _⟩
  rw [@isOpen_iff_preimages_plots _ ⊥ u]; intro n p hp
  let ⟨x,hx⟩ := DiffeologicalSpace.eq_bot_iff.1 rfl n p hp
  by_cases h : x ∈ u; all_goals simp [hx,h]

/-- The discrete diffeologoy is the only diffeology whose D-topology is discrete.
  Note that the corresponding statement for indiscrete spaces is false. -/
theorem dTop_eq_bot_iff {X : Type*} {dX : DiffeologicalSpace X} : DTop[dX] = ⊥ ↔ dX = ⊥ := by
  refine' ⟨fun h => _,fun h => by rw [h,dTop_bot]⟩
  refine' (dX.eq_bot_iff).2 fun n p hp => ⟨p 0,funext fun x => _⟩
  exact @PreconnectedSpace.constant _ _ X ⊥ (discreteTopology_bot X) inferInstance
    p (h ▸ hp.continuous) _ _

/-- A map from an indiscrete space is smooth iff its range is indiscrete.
  Note that this can't be characterised purely topologically, since it might be the case that
  all involved D-topologies are indiscrete but the diffeologies are not. -/
theorem dsmooth_top_iff_indiscrete_range {X Y : Type*} {dY : DiffeologicalSpace Y} {f : X → Y} :
    DSmooth[⊤,dY] f ↔ @instDiffeologicalSpaceSubtype Y dY (Set.range f) = ⊤ := by
  let _ : DiffeologicalSpace X := ⊤
  refine' ⟨fun hf => _,fun h => _⟩
  · refine' DiffeologicalSpace.eq_top_iff.2 fun n p => _
    have hf' : DSmooth (Set.rangeFactorization f) := hf.codRestrict mem_range_self
    let ⟨g,hg⟩ := (Set.surjective_onto_range (f := f)).hasRightInverse
    have h := hf' n (g ∘ p) trivial
    rw [←Function.comp.assoc,hg.id,Function.id_comp] at h; exact h
  · exact dsmooth_subtype_val.comp (h ▸ dsmooth_top : DSmooth (Set.rangeFactorization f))

/-- A map to an discrete space is smooth iff it is D-locally constant. -/
theorem dsmooth_bot_iff_isLocallyConstant {X Y : Type*} {dX : DiffeologicalSpace X} {f : X → Y} :
    DSmooth[dX,⊥] f ↔ @IsLocallyConstant _ _ DTop[dX] f:= by
  refine' ⟨fun hf _ => _,@IsLocallyConstant.dsmooth _ dX Y ⊥ _⟩
  exact @IsOpen.preimage _ Y DTop[dX] ⊥ _ (dTop_bot ▸ @DSmooth.continuous _ Y dX ⊥ _ hf) _ trivial

open PartialHomeomorph in
/-- A map is a plot in the coinduced diffeology iff it is constant or lifts locally.
  TODO: golf this using `DiffeologicalSpace.mkOfPlotsOn`? -/
theorem isPlot_coinduced_iff {X Y : Type*} {dX : DiffeologicalSpace X} {f : X → Y}
    {n : ℕ} {p : Eucl n → Y} : IsPlot[dX.coinduced f] p ↔ (∃ y, p = fun _ => y) ∨
    ∀ x : Eucl n, ∃ u, IsOpen u ∧ x ∈ u ∧ ∃ p' : u → X, DSmooth p' ∧ p ∘ (↑) = f ∘ p' := by
  let dY := dX.coinduced f
  refine' ⟨fun hp => _,Or.rec (fun ⟨y,hy⟩ => hy ▸ isPlot_const) fun h => _⟩
  · let d : DiffeologicalSpace Y := {
      plots := fun n => {p | (∃ y, p = fun _ => y) ∨
        ∀ x : Eucl n, ∃ u , IsOpen u ∧ x ∈ u ∧ ∃ p' : u → X, DSmooth p' ∧ p ∘ (↑) = f ∘ p'}
      constant_plots := fun x => Or.inl ⟨x,rfl⟩
      plot_reparam := fun {n m p g} hp hg => Or.rec (fun ⟨y,hy⟩ => Or.inl ⟨y,hy ▸ rfl⟩)
        (fun h => Or.inr fun x => (by
          let ⟨u,hu,hxu,p',hp',hp''⟩ := h (g x)
          refine' ⟨g ⁻¹' u,hu.preimage hg.continuous,hxu,p' ∘ u.restrictPreimage g,
          hp'.comp hg.dsmooth.restrictPreimage,_⟩
          simp_rw [←Function.comp.assoc,←hp'',Function.comp.assoc]; rfl)) hp
      locality := fun {n p} h => by
        replace h : ∀ x : Eucl n, ∃ u, IsOpen u ∧ x ∈ u ∧
            (p x ∉ range f → u.restrict p = fun _ => p x) ∧
            (p x ∈ range f → ∃ p' : u → X, DSmooth p' ∧ p ∘ (↑) = f ∘ p') := fun x => by
          let ⟨u,hu,hxu,hu'⟩ := h x; let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 hu x hxu
          have hx := Metric.mem_ball_self hε (x := x)
          let e : Eucl n ≃ₜ Metric.ball x ε := (Homeomorph.Set.univ _).symm.trans <|
            univUnitBall.toHomeomorphSourceTarget.trans
              (unitBallBall x ε hε).toHomeomorphSourceTarget
          have he : DSmooth (((↑) : _ → Eucl n) ∘ e) :=
            (contDiff_unitBallBall hε).dsmooth.comp
              contDiff_univUnitBall.dsmooth
          have he' : DSmooth e.symm := by
            have h₁ : DSmooth (univUnitBall (E := Eucl n)).toHomeomorphSourceTarget.symm :=
              ContDiffOn.dsmooth_restrict (contDiffOn_univUnitBall_symm (n := ⊤) (E := Eucl n))
            have h₂ : DSmooth (unitBallBall x ε hε).toHomeomorphSourceTarget.symm :=
              (contDiff_unitBallBall_symm (n := ⊤) (c := x) hε).dsmooth.restrict
                ((unitBallBall x ε hε).symm_mapsTo)
            exact (dsmooth_subtype_val.comp (h₁.comp h₂):)
          specialize hu' (by exact fun x'' => hε' (e x'').2) he.contDiff; dsimp at hu'
          obtain ⟨x',hx'⟩ | hpx := @or_not (p x ∈ range f)
          · obtain ⟨y,hy⟩ | hu' := hu'
            · refine' ⟨_,Metric.isOpen_ball,hx,fun h => (h ⟨x',hx'⟩).elim,fun _ => _⟩
              have h := congrFun hy (e.symm ⟨x,hx⟩)
              simp_rw [Function.comp_apply, Homeomorph.apply_symm_apply] at h
              refine' ⟨fun _ => x',dsmooth_const,_⟩
              rw [←Function.comp_id (f := Subtype.val),←Homeomorph.self_comp_symm e,
                ←Function.comp.assoc _ e,←Function.comp.assoc,hy,←h,←hx']; rfl
            · let ⟨v,hv,hxv,p',hp'⟩ := hu' (e.symm ⟨x,hx⟩)
              refine' ⟨Subtype.val '' (e.symm ⁻¹' v),Metric.isOpen_ball.isOpenMap_subtype_val _
                (hv.preimage e.symm.continuous),⟨_,hxv,by simp⟩,fun h => (h ⟨x',hx'⟩).elim,fun _ => _⟩
              use p' ∘ (v.restrictPreimage e.symm) ∘ (fun x => ⟨⟨x.1,
                (Subtype.range_val ▸ image_subset_range _ _ x.2 :)⟩,
                  Subtype.val_injective.mem_set_image.1 x.2⟩)
              refine' ⟨hp'.1.comp <| he'.restrictPreimage.comp <| DSmooth.subtype_mk
                (DSmooth.subtype_mk dsmooth_subtype_val _) _,_⟩
              rw [←Function.comp.assoc,←hp'.2]; ext x; simp
          · refine' ⟨_,Metric.isOpen_ball,hx,fun _ => _,fun h => (hpx h).elim⟩
            let ⟨y,hy⟩ := (or_iff_left (fun h => hpx <| by
              let ⟨v,_,hxv,p',_,hp'⟩ := h (e.symm ⟨x,hx⟩)
              have h := congrFun hp' ⟨_,hxv⟩
              simp_rw [Function.comp_apply, Homeomorph.apply_symm_apply] at h
              exact ⟨_,h.symm⟩)).1 hu'
            rw [restrict_eq,←Function.comp_id (f := Subtype.val),←Homeomorph.self_comp_symm e,
              ←Function.comp.assoc _ e,←Function.comp.assoc,hy]
            have h := congrFun hy (e.symm ⟨x,hx⟩)
            simp_rw [Function.comp_apply, Homeomorph.apply_symm_apply] at h
            rw [h]; rfl
        have h' : IsClopen (p ⁻¹' (range f)) := by
          refine' ⟨⟨isOpen_iff_mem_nhds.2 fun x hx => _⟩,isOpen_iff_mem_nhds.2 fun x hx => _⟩
          all_goals let ⟨u,hu,hxu,hu'⟩ := h x; rw [mem_nhds_iff]; refine' ⟨u,_,hu,hxu⟩
          · refine' fun x' hx' => (_ : p x' ∉ range f)
            rw [(by exact congrFun (hu'.1 hx) ⟨x',hx'⟩ : p x' = p x)]; exact hx
          · let ⟨p',_,(hp' : u.restrict p = _)⟩ := hu'.2 hx
            rw [←image_subset_iff,←range_restrict,hp']; exact range_comp_subset_range p' f
        cases' isClopen_iff.1 h' with h' h'
        · left; have := Nonempty.map p inferInstance
          refine' IsLocallyConstant.exists_eq_const <| (IsLocallyConstant.iff_exists_open p).2 _
          intro x; let ⟨u,hu,hxu,hu',_⟩ := h x
          exact ⟨u,hu,hxu,fun x' hx' => congrFun (hu' (h'.symm ▸ not_mem_empty x:)) ⟨x',hx'⟩⟩
        · right; intro x; let ⟨u,hu,hxu,_,hu'⟩ := h x
          exact ⟨u,hu,hxu,hu' (h'.symm ▸ mem_univ x:)⟩
    }
    have hd : dY ≤ d := sInf_le fun n p hp => Or.inr fun x => ⟨_,isOpen_univ,mem_univ x,
      p ∘ (Equiv.Set.univ _),hp.dsmooth.comp dsmooth_subtype_val,rfl⟩
    exact DiffeologicalSpace.le_iff'.1 hd n p hp
  · refine' isPlot_iff_locally_dsmooth.2 fun x => Exists.imp (fun u ⟨hu,hxu,p',hp'⟩ => _) (h x)
    rw [Set.restrict_eq,hp'.2]
    exact ⟨hu,hxu,dsmooth_coinduced_rng.comp hp'.1⟩

/-- For surjective functions, the plots of the coinduced diffeology are precicely those that
  locally lift. -/
theorem Function.Surjective.isPlot_coinduced_iff {X Y : Type*} {dX : DiffeologicalSpace X}
    {f : X → Y} (hf : Function.Surjective f) {n : ℕ} {p : Eucl n → Y} : IsPlot[dX.coinduced f] p ↔
    ∀ x : Eucl n, ∃ u, IsOpen u ∧ x ∈ u ∧ ∃ p' : u → X, DSmooth p' ∧ p ∘ (↑) = f ∘ p' := by
  refine' _root_.isPlot_coinduced_iff.trans ⟨fun h => Or.elim h (fun ⟨y,hy⟩ x => _) id,Or.inr⟩
  let ⟨x',hx'⟩ := hf y
  exact ⟨_,isOpen_univ,mem_univ x,fun _ => x',dsmooth_const,funext fun x => hy ▸ hx' ▸ rfl⟩

open Classical in
/-- The D-topology of the coinduced diffeology agrees with the coinduced topology.
  TODO: refactor definitions to make this a definitional equality. -/
theorem dTop_coinduced_comm {X Y : Type*} {dX : DiffeologicalSpace X} {f : X → Y} :
    DTop[dX.coinduced f] = DTop[dX].coinduced f := by
  let _ := dX.coinduced f; let _ := @DTop X _
  let hf : DSmooth f := by rw [dsmooth_iff_coinduced_le]
  refine' le_antisymm (TopologicalSpace.le_def.2 fun u hu => _) _
  · rw [isOpen_iff_preimages_plots]; intro n p hp
    rw [isOpen_coinduced] at hu
    obtain ⟨y,hy⟩ | hp := isPlot_coinduced_iff.1 hp
    · by_cases h : y ∈ u; all_goals simp [hy,h]
    · refine' isOpen_iff_mem_nhds.2 fun x hx => _
      let ⟨v,hv,hxv,p',hp',hp⟩ := hp x
      refine' mem_nhds_iff.2 ⟨_,inter_subset_right v _,_,hxv,hx⟩
      rw [←Subtype.image_preimage_val,←preimage_comp,hp,preimage_comp]
      exact hv.isOpenMap_subtype_val _ (hu.preimage (hv.dTopCompatible.dTop_eq ▸ hp'.continuous))
  · exact continuous_iff_coinduced_le.1 <| hf.continuous

/-- The D-topology is coinduced by all plots. -/
lemma dTop_eq_iSup_coinduced {X : Type*} [dX : DiffeologicalSpace X] :
    DTop = ⨆ (p : (n : ℕ) × dX.plots n), coinduced p.2.1 inferInstance := by
  ext u
  rw [isOpen_iff_preimages_plots,isOpen_iSup_iff,Sigma.forall]; simp_rw [isOpen_coinduced]
  exact forall_congr' fun n => ⟨fun h p => h p p.2,fun h p hp => h ⟨p,hp⟩⟩

/-- The D-topology is coinduced by the sum of all plots. -/
lemma dTop_eq_coinduced {X : Type*} [dX : DiffeologicalSpace X] : DTop =
    coinduced (fun x : (p : (n : ℕ) × dX.plots n) × Eucl p.1 ↦ x.1.2.1 x.2) inferInstance := by
  rw [dTop_eq_iSup_coinduced, ← coinduced_sigma]

/-- The D-topology is always delta-generated. -/
instance instDeltaGeneratedSpaceDTop {X : Type*} [DiffeologicalSpace X] :
    @DeltaGeneratedSpace X DTop := by
  let _ : TopologicalSpace X := DTop; refine' ⟨_⟩
  nth_rewrite 1 [dTop_eq_iSup_coinduced,deltaGenerated]
  refine' iSup_le fun ⟨n,p⟩ => _
  let e : (Fin n → ℝ) ≃L[ℝ] Eucl _ := toEuclidean
  rw [FiniteDimensional.finrank_pi,Fintype.card_fin] at e
  refine' le_trans _ <| le_iSup _ (⟨n,@ContinuousMap.mk (Fin n → ℝ) X _ (_:) (p.1 ∘ e) <|
    (IsPlot.dsmooth p.2).continuous.comp e.continuous⟩)
  simp only [←coinduced_compose,ContinuousMap.coe_mk]
  rw [show coinduced e _ = _ by exact e.toHomeomorph.coinduced_eq]

/-- Diffeological spaces are always delta-generated when equipped with the D-topology. -/
instance {X : Type*} [DiffeologicalSpace X] [TopologicalSpace X] [DTopCompatible X] :
    DeltaGeneratedSpace X :=
  dTop_eq (X := X) ▸ inferInstance

end DTop

section Quotient

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]
  {r : X → X → Prop} {s : Setoid X}

theorem subduction_quot_mk : Subduction (@Quot.mk X r) :=
  ⟨Quot.exists_rep, rfl⟩

theorem dsmooth_quot_mk : DSmooth (@Quot.mk X r) :=
  dsmooth_coinduced_rng

theorem dsmooth_quot_lift {f : X → Y} (hr : ∀ a b, r a b → f a = f b) (h : DSmooth f) :
    DSmooth (Quot.lift f hr : Quot r → Y) :=
  dsmooth_coinduced_dom.2 h

theorem subduction_quotient_mk' : Subduction (@Quotient.mk' X s) :=
  subduction_quot_mk

theorem dsmooth_quotient_mk' : DSmooth (@Quotient.mk' X s) :=
  dsmooth_coinduced_rng

theorem DSmooth.quotient_lift {f : X → Y} (h : DSmooth f) (hs : ∀ a b, a ≈ b → f a = f b) :
    DSmooth (Quotient.lift f hs : Quotient s → Y) :=
  dsmooth_coinduced_dom.2 h

theorem DSmooth.quotient_liftOn' {f : X → Y} (h : DSmooth f)
    (hs : ∀ a b, @Setoid.r _ s a b → f a = f b) :
    DSmooth (fun x => Quotient.liftOn' x f hs : Quotient s → Y) :=
  h.quotient_lift hs

theorem DSmooth.quotient_map' {t : Setoid Y} {f : X → Y} (hf : DSmooth f)
    (H : (s.r ⇒ t.r) f f) : DSmooth (Quotient.map' f H) :=
  (dsmooth_quotient_mk'.comp hf).quotient_lift _

/-- The plots of the quotient diffeology are precicely those that locally lift to plots. -/
theorem isPlot_quot_iff {n : ℕ} {p : Eucl n → Quot r} : IsPlot p ↔ ∀ x : Eucl n,
    ∃ u, IsOpen u ∧ x ∈ u ∧ ∃ p' : u → X, DSmooth p' ∧ p ∘ (↑) = (@Quot.mk X r) ∘ p' :=
  (surjective_quot_mk r).isPlot_coinduced_iff

/-- The plots of the quotient diffeology are precicely those that locally lift to plots. -/
theorem isPlot_quotient_iff {n : ℕ} {p : Eucl n → Quotient s} : IsPlot p ↔ ∀ x : Eucl n,
    ∃ u, IsOpen u ∧ x ∈ u ∧ ∃ p' : u → X, DSmooth p' ∧ p ∘ (↑) = (@Quotient.mk X s) ∘ p' :=
  Function.Surjective.isPlot_coinduced_iff (by exact Quot.exists_rep)

instance [TopologicalSpace X] [DTopCompatible X] : DTopCompatible (Quot r) :=
  ⟨dTop_eq X ▸ dTop_coinduced_comm⟩

instance [TopologicalSpace X] [DTopCompatible X] : DTopCompatible (Quotient s) :=
  ⟨dTop_eq X ▸ dTop_coinduced_comm⟩

end Quotient

section Prod

variable {X Y Z W ε ζ: Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]
  [DiffeologicalSpace W] [DiffeologicalSpace ε] [DiffeologicalSpace ζ]

@[simp]
theorem dsmooth_prod_mk {f : X → Y} {g : X → Z} :
    DSmooth (fun x => (f x,g x)) ↔ DSmooth f ∧ DSmooth g :=
  dsmooth_inf_rng

theorem dsmooth_fst : DSmooth (@Prod.fst X Y) :=
  (dsmooth_prod_mk.1 dsmooth_id).1

@[fun_prop]
theorem DSmooth.fst {f : X → Y × Z} (hf : DSmooth f) : DSmooth fun x => (f x).1 :=
  dsmooth_fst.comp hf

theorem DSmooth.fst' {f : X → Z} (hf : DSmooth f) : DSmooth fun x : X × Y => f x.fst :=
  hf.comp dsmooth_fst

theorem dsmooth_snd : DSmooth (@Prod.snd X Y) :=
  (dsmooth_prod_mk.1 dsmooth_id).2

@[fun_prop]
theorem DSmooth.snd {f : X → Y × Z} (hf : DSmooth f) : DSmooth fun x => (f x).2 :=
  dsmooth_snd.comp hf

theorem DSmooth.snd' {f : Y → Z} (hf : DSmooth f) : DSmooth fun x : X × Y => f x.snd :=
  hf.comp dsmooth_snd

@[fun_prop]
theorem DSmooth.prod_mk {f : Z → X} {g : Z → Y} (hf : DSmooth f) (hg : DSmooth g) :
    DSmooth fun x => (f x, g x) :=
  dsmooth_prod_mk.2 ⟨hf, hg⟩

theorem DSmooth.Prod.mk (x : X) : DSmooth fun y : Y => (x, y) :=
  dsmooth_const.prod_mk dsmooth_id

theorem DSmooth.Prod.mk_left (y : Y) : DSmooth fun x : X => (x, y) :=
  dsmooth_id.prod_mk dsmooth_const

theorem DSmooth.comp₂ {g : X × Y → Z} (hg : DSmooth g) {e : W → X} (he : DSmooth e)
    {f : W → Y} (hf : DSmooth f) : DSmooth fun w => g (e w, f w) :=
  hg.comp <| he.prod_mk hf

theorem DSmooth.comp₃ {g : X × Y × Z → ε} (hg : DSmooth g) {e : W → X} (he : DSmooth e)
    {f : W → Y} (hf : DSmooth f) {k : W → Z} (hk : DSmooth k) :
    DSmooth fun w => g (e w, f w, k w) :=
  hg.comp₂ he <| hf.prod_mk hk

theorem DSmooth.comp₄ {g : X × Y × Z × ζ → ε} (hg : DSmooth g) {e : W → X} (he : DSmooth e)
    {f : W → Y} (hf : DSmooth f) {k : W → Z} (hk : DSmooth k) {l : W → ζ}
    (hl : DSmooth l) : DSmooth fun w => g (e w, f w, k w, l w) :=
  hg.comp₃ he hf <| hk.prod_mk hl

theorem DSmooth.prod_map {f : Z → X} {g : W → Y} (hf : DSmooth f) (hg : DSmooth g) :
    DSmooth fun p : Z × W => (f p.1, g p.2) :=
  hf.fst'.prod_mk hg.snd'

/-- A version of `dsmooth_inf_dom_left` for binary functions -/
theorem dsmooth_inf_dom_left₂ {X Y Z} {f : X → Y → Z} {dX dX' : DiffeologicalSpace X}
    {dY dY' : DiffeologicalSpace Y} {dZ : DiffeologicalSpace Z}
    (h : by haveI := dX; haveI := dY; exact DSmooth fun p : X × Y => f p.1 p.2) : by
    haveI := dX ⊓ dX'; haveI := dY ⊓ dY'; exact DSmooth fun p : X × Y => f p.1 p.2 := by
  have ha := @dsmooth_inf_dom_left _ _ dX dX dX' id (@dsmooth_id _ (id _))
  have hb := @dsmooth_inf_dom_left _ _ dY dY dY' id (@dsmooth_id _ (id _))
  have h_dsmooth_id := @DSmooth.prod_map _ _ _ _ dX dY (dX ⊓ dX') (dY ⊓ dY') _ _ ha hb
  exact @DSmooth.comp _ _ _ (id _) (id _) _ _ _ h h_dsmooth_id

/-- A version of `dsmooth_inf_dom_right` for binary functions -/
theorem dsmooth_inf_dom_right₂ {X Y Z} {f : X → Y → Z} {dX dX' : DiffeologicalSpace X}
    {dY dY' : DiffeologicalSpace Y} {dZ : DiffeologicalSpace Z}
    (h : by haveI := dX'; haveI := dY'; exact DSmooth fun p : X × Y => f p.1 p.2) : by
    haveI := dX ⊓ dX'; haveI := dY ⊓ dY'; exact DSmooth fun p : X × Y => f p.1 p.2 := by
  have ha := @dsmooth_inf_dom_right _ _ dX dX' dX' id (@dsmooth_id _ (id _))
  have hb := @dsmooth_inf_dom_right _ _ dY dY' dY' id (@dsmooth_id _ (id _))
  have h_dsmooth_id := @DSmooth.prod_map _ _ _ _ dX' dY' (dX ⊓ dX') (dY ⊓ dY') _ _ ha hb
  exact @DSmooth.comp _ _ _ (id _) (id _) _ _ _ h h_dsmooth_id

/-- A version of `dsmooth_sInf_dom` for binary functions -/
theorem dsmooth_sInf_dom₂ {X Y Z} {f : X → Y → Z} {DX : Set (DiffeologicalSpace X)}
    {DY : Set (DiffeologicalSpace Y)} {tX : DiffeologicalSpace X} {tY : DiffeologicalSpace Y}
    {tc : DiffeologicalSpace Z} (hX : tX ∈ DX) (hY : tY ∈ DY)
    (hf : DSmooth fun p : X × Y => f p.1 p.2) : by
    haveI := sInf DX; haveI := sInf DY;
      exact @DSmooth _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := dsmooth_sInf_dom hX dsmooth_id
  have hY := dsmooth_sInf_dom hY dsmooth_id
  have h_dsmooth_id := @DSmooth.prod_map _ _ _ _ tX tY (sInf DX) (sInf DY) _ _ hX hY
  exact @DSmooth.comp _ _ _ (id _) (id _) _ _ _ hf h_dsmooth_id

theorem dsmooth_swap : DSmooth (Prod.swap : X × Y → Y × X) :=
  dsmooth_snd.prod_mk dsmooth_fst

theorem DSmooth.uncurry_left {f : X → Y → Z} (x : X) (h : DSmooth (Function.uncurry f)) :
    DSmooth (f x) :=
  h.comp (DSmooth.Prod.mk _)

theorem DSmooth.uncurry_right {f : X → Y → Z} (y : Y) (h : DSmooth (Function.uncurry f)) :
    DSmooth fun a => f a y :=
  h.comp (DSmooth.Prod.mk_left _)

theorem dsmooth_curry {g : X × Y → Z} (x : X) (h : DSmooth g) : DSmooth (Function.curry g x) :=
  DSmooth.uncurry_left x h

/-- Smooth functions on products are smooth in their first argument -/
theorem DSmooth.curry_left {f : X × Y → Z} (hf : DSmooth f) {y : Y} :
    DSmooth fun x ↦ f (x, y) :=
  hf.comp (dsmooth_id.prod_mk dsmooth_const)
alias DSmooth.along_fst := DSmooth.curry_left

/-- Smooth functions on products are smooth in their second argument -/
theorem DSmooth.curry_right {f : X × Y → Z} (hf : DSmooth f) {x : X} :
    DSmooth fun y ↦ f (x, y) :=
  hf.comp (dsmooth_const.prod_mk dsmooth_id)
alias DSmooth.along_snd := DSmooth.curry_right

theorem IsPlot.prod {n} {p : Eucl n → X} {p' : Eucl n → Y} (hp : IsPlot p) (hp' : IsPlot p') :
    IsPlot (fun x => (p x,p' x)) :=
  (hp.dsmooth.prod_mk hp'.dsmooth).isPlot

theorem isPlot_prod_iff {n} {p : Eucl n → X × Y} :
    IsPlot p ↔ IsPlot (fun x => (p x).1) ∧ IsPlot (fun x => (p x).2) :=
  ⟨fun hp => ⟨hp.dsmooth.fst.isPlot,hp.dsmooth.snd.isPlot⟩,fun h => h.1.prod h.2⟩

/-- The first projection in a product of diffeological spaces is a subduction. -/
theorem subduction_fst [Nonempty Y] : Subduction (@Prod.fst X Y) := by
  let y : Y := Nonempty.some inferInstance
  have h : Function.LeftInverse (@Prod.fst X Y) fun x => (x,y) := fun _ => rfl
  exact h.subduction dsmooth_fst dsmooth_id.curry_left

/-- The second projection in a product of diffeological spaces is a subduction. -/
theorem subduction_snd [Nonempty X] : Subduction (@Prod.snd X Y) := by
  let x : X := Nonempty.some inferInstance
  have h : Function.LeftInverse (@Prod.snd X Y) fun y => (x,y) := fun _ => rfl
  exact h.subduction dsmooth_snd dsmooth_id.curry_right

/-- A product of induced diffeologies is induced by the product map. -/
theorem DiffeologicalSpace.prod_induced_induced (f : X → Y) (g : Z → W) :
    @instDiffeologicalSpaceProd X Z (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) instDiffeologicalSpaceProd := by
  delta instDiffeologicalSpaceProd; simp_rw [induced_inf, induced_compose]; rfl

/-- The diffeology coinduced by a product map is at least as fine as the product of the
  coinduced diffelogies. Note that equality only holds when both maps are surjective. -/
theorem DiffeologicalSpace.coinduced_prod_le {X Y Z W : Type*}
    [dX : DiffeologicalSpace X] [dZ : DiffeologicalSpace Z] (f : X → Y) (g : Z → W) :
    coinduced (fun p => (f p.1, g p.2)) instDiffeologicalSpaceProd ≤
      @instDiffeologicalSpaceProd Y W (coinduced f dX) (coinduced g dZ) :=
  let _ := dX.coinduced f; let _ := dZ.coinduced g
  dsmooth_iff_coinduced_le.1 (dsmooth_coinduced_rng.prod_map dsmooth_coinduced_rng)

/-- A product of coinduced diffeologies is coinduced by the product map, if both maps
  are surjective. -/
theorem DiffeologicalSpace.prod_coinduced_coinduced {X Y Z W : Type*}
    [dX : DiffeologicalSpace X] [dZ : DiffeologicalSpace Z] {f : X → Y} {g : Z → W}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    @instDiffeologicalSpaceProd Y W (coinduced f dX) (coinduced g dZ) =
      coinduced (fun p => (f p.1, g p.2)) instDiffeologicalSpaceProd := by
  let _ := dX.coinduced f; let _ := dZ.coinduced g
  refine' le_antisymm (DiffeologicalSpace.le_iff'.2 fun n p hp => _) (coinduced_prod_le _ _)
  simp_rw [isPlot_prod_iff,hf.isPlot_coinduced_iff,hg.isPlot_coinduced_iff] at hp
  refine' (hf.Prod_map hg).isPlot_coinduced_iff.2 fun x => _
  let ⟨u₁,hu₁,hxu₁,p₁,hp₁⟩ := hp.1 x; let ⟨u₂,hu₂,hxu₂,p₂,hp₂⟩ := hp.2 x
  refine' ⟨_,hu₁.inter hu₂,⟨hxu₁,hxu₂⟩,_,DSmooth.prod_mk
    (hp₁.1.comp (dsmooth_inclusion (inter_subset_left _ u₂)))
    (hp₂.1.comp (dsmooth_inclusion (inter_subset_right _ u₂))),funext fun x => _⟩
  simp_rw [Function.comp,Prod_map,←f.comp_apply,←hp₁.2,←g.comp_apply,←hp₂.2]; rfl


theorem Induction.prod_map {f : X → Y} {g : Z → W} (hf : Induction f) (hg : Induction g) :
    Induction (Prod.map f g) :=
  ⟨hf.1.Prod_map hg.1,by rw [hf.2,hg.2,DiffeologicalSpace.prod_induced_induced f g]; rfl⟩

theorem Subduction.prod_map {f : X → Y} {g : Z → W} (hf : Subduction f) (hg : Subduction g) :
    Subduction (Prod.map f g) :=
  ⟨hf.1.Prod_map hg.1,by rw [hf.2,hg.2,DiffeologicalSpace.prod_coinduced_coinduced hf.1 hg.1]; rfl⟩

@[simp]
theorem induction_const_prod {x : X} {f : Y → Z} :
    (Induction fun y => (x, f y)) ↔ Induction f := by
  refine' and_congr ((Prod.mk.inj_left x).of_comp_iff f) _
  simp_rw [instDiffeologicalSpaceProd, DiffeologicalSpace.induced_inf,
    DiffeologicalSpace.induced_compose, Function.comp,
    DiffeologicalSpace.induced_const, top_inf_eq]

@[simp]
theorem induction_prod_const {y : Y} {f : X → Z} :
    (Induction fun x => (f x, y)) ↔ Induction f := by
  refine' and_congr ((Prod.mk.inj_right y).of_comp_iff f) _
  simp_rw [instDiffeologicalSpaceProd, DiffeologicalSpace.induced_inf,
    DiffeologicalSpace.induced_compose, Function.comp,
    DiffeologicalSpace.induced_const, inf_top_eq]

theorem induction_graph {f : X → Y} (hf : DSmooth f) : Induction fun x => (x, f x) :=
  Induction.of_comp' (dsmooth_id.prod_mk hf) dsmooth_fst induction_id

theorem induction_prod_mk (x : X) : Induction (Prod.mk x : Y → X × Y) :=
  induction_const_prod.2 induction_id

theorem induction_prod_mk_left (y : X) : Induction (fun x : X => (x, y)) :=
  induction_prod_const.2 induction_id

/-- Products of reflexive diffeological spaces are reflexive. -/
instance [hX : ReflexiveDiffeologicalSpace X] [hY :ReflexiveDiffeologicalSpace Y] :
    ReflexiveDiffeologicalSpace (X × Y) where
  isPlot_if p h :=
    (hX.isPlot_if (fun x => (p x).1) fun _ hf => h _ <| hf.fst').prod <|
      hY.isPlot_if (fun x => (p x).2) fun _ hf => h _ <| hf.snd'

/-- Products of normed spaces are compatible with the product diffeology. -/
instance {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X]
    [ContDiffCompatible X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [DiffeologicalSpace Y]
    [ContDiffCompatible Y] : ContDiffCompatible (X × Y) := ⟨fun {n p} ↦ by
  simp_rw [isPlot_prod_iff, isPlot_iff_contDiff]
  exact ⟨fun h ↦ h.1.prod h.2, fun h ↦ ⟨h.fst, h.snd⟩⟩⟩

/-- The D-topology of the product diffeology is at least as fine as the product of
  the D-topologies. -/
theorem dTop_prod_le_prod_dTop :
    (DTop : TopologicalSpace (X × Y)) ≤ @instTopologicalSpaceProd _ _ DTop DTop :=
  continuous_id_iff_le.1 ((@continuous_prod_mk _ X Y DTop DTop DTop _ _).2
    ⟨dsmooth_fst.continuous,dsmooth_snd.continuous⟩)

/-- For locally compact spaces `X`, the product functor `X × -` takes quotient maps to quotient
  maps. Note that surjectivity is actually required here - coinducing maps do not necessarily
  get taken to coinducing maps.
  Adapted from
  https://dantopology.wordpress.com/2023/04/21/the-product-of-the-identity-map-and-a-quotient-map/.
  TODO: give an explicit description of the coinduced topology without assuming surjectivity
  TODO: give an explicit description even without local compactness, using `deltaGenerated`
  TODO: maybe move to mathlib? -/
theorem QuotientMap.id_prod {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace X] {f : Y → Z} (hf : QuotientMap f) :
    QuotientMap (Prod.map (@id X) f) := by
  refine ⟨Function.surjective_id.Prod_map hf.1,
    le_antisymm ?_ (continuous_id.prod_map hf.continuous).coinduced_le⟩
  intro s hs; rw [isOpen_coinduced] at hs
  refine isOpen_prod_iff.mpr fun x z hxz ↦ ?_
  let ⟨y, hy⟩ := hf.1 z
  let ⟨k, hk, hks, hk'⟩ := local_compact_nhds <|
    (hs.preimage <| continuous_id.prod_mk continuous_const).mem_nhds (hy.symm ▸ hxz)
  let ⟨u, huk, hu, hxu⟩ := mem_nhds_iff.mp hk
  refine ⟨u, {z | k ×ˢ (f ⁻¹' {z}) ⊆ Prod.map id f ⁻¹' s}, hu, ?_, hxu, ?_, ?_⟩
  · rw [hf.2, isOpen_coinduced]; dsimp
    have : CompactSpace k := isCompact_iff_compactSpace.mp hk'
    suffices h : IsOpen {y | k ×ˢ {y} ⊆ Prod.map id f ⁻¹' s} by
      convert h using 1; ext y
      simp_rw [← image_subset_iff, Prod.map, ← prod_image_image_eq,
        image_preimage_eq _ hf.1, image_singleton]
    have h := (isClosedMap_snd_of_compactSpace (X := k) (Prod.map (↑) f ⁻¹' s)ᶜ <|
      IsOpen.isClosed_compl
      (by exact hs.preimage (continuous_subtype_val.prod_map continuous_id))).isOpen_compl
    convert h using 1; ext y'
    simp [prod_subset_iff, - prod_singleton]
  · intro ⟨x', y'⟩ hxy'
    rw [mem_preimage, Prod_map, (hxy'.2 : f _ = _), ← hy]
    exact hks hxy'.1
  · intro ⟨x', z'⟩ hxz'; let ⟨y', hy'⟩ := hf.1 z'
    exact hy' ▸ hxz'.2 (by exact ⟨huk hxz'.1, hy'⟩ : (x', y') ∈ _)

/-- Analogous to `QuotientMap.id_prod`. -/
theorem QuotientMap.prod_id {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Z] {f : X → Y} (hf : QuotientMap f) :
    QuotientMap (Prod.map f (@id Z)) := by
  exact (Homeomorph.prodComm _ _).quotientMap.comp <|
    (hf.id_prod (X := Z)).comp (Homeomorph.prodComm _ _).quotientMap

/-- Equivalent of `Function.Surjective.sigma_map` for quotient maps.
  TODO: move to mathlib. -/
theorem QuotientMap.sigma_map {ι ι' : Type*} {X : ι → Type*} {Y : ι' → Type*}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι') → TopologicalSpace (Y i)] {f₁ : ι → ι'}
    {f₂ : (i : ι) → X i → Y (f₁ i)} (h₁ : Function.Surjective f₁)
    (h₂ : ∀ i : ι, QuotientMap (f₂ i)) : QuotientMap (Sigma.map f₁ f₂) :=
  ⟨h₁.sigma_map fun i ↦ (h₂ i).1, by
    ext u; simp_rw [isOpen_coinduced, isOpen_sigma_iff, h₁.forall]
    exact forall_congr' fun i => (h₂ i).2 ▸ isOpen_coinduced⟩

-- TODO: move to mathlib? also figure out why this works below but `coinduced_sigma` doesn't
lemma coinduced_sigma' {ι Y : Type*} {X : ι → Type v} [tX : (i : ι) → TopologicalSpace (X i)]
    (f : (i : ι) × X i → Y) : coinduced f inferInstance =
    ⨆ i : ι, coinduced (fun x ↦ f ⟨i,x⟩) inferInstance := by
  rw [instTopologicalSpaceSigma,coinduced_iSup]; rfl

/-- For locally compact diffeological spaces, the D-topology commutes with products.
  This is not true in general, because the product topology might not be delta-generated;
  however, according to a remark in https://arxiv.org/abs/1302.2935 it should be always true
  if one takes the product in the category of delta-generated spaces instead of in Top.
  TODO: work this all out more generally -/
theorem dTop_prod_eq_prod_dTop [@LocallyCompactSpace X DTop] :
    (DTop : TopologicalSpace (X × Y)) = @instTopologicalSpaceProd _ _ DTop DTop := by
  let _ := @DTop X _; let _ := @DTop Y _
  refine le_antisymm dTop_prod_le_prod_dTop ?_
  have h₁ := @QuotientMap.id_prod X _ Y _ _ _ _ _
    ⟨fun y => ⟨⟨⟨37, ⟨fun _ => y, isPlot_const⟩⟩, 0⟩, rfl⟩, dTop_eq_coinduced⟩
  have h₂ := @QuotientMap.comp _ _ _ _ _ _ _ (@instTopologicalSpaceProd X Y _ DTop) h₁ <|
    (Homeomorph.sigmaProdDistrib.symm.trans (Homeomorph.prodComm _ _)).quotientMap.comp
      (QuotientMap.sigma_map Function.surjective_id fun i => (QuotientMap.id_prod
        ⟨fun x => ⟨⟨⟨37, ⟨fun _ => x, isPlot_const⟩⟩, 0⟩, rfl⟩, dTop_eq_coinduced⟩).comp <|
          (Homeomorph.sigmaProdDistrib.symm.trans (Homeomorph.prodComm _ _)).quotientMap.comp <|
            QuotientMap.sigma_map Function.surjective_id fun i ↦
              toEuclidean.symm.toHomeomorph.quotientMap)
  simp_rw [h₂.2,coinduced_sigma',iSup_le_iff]
  intro p₁ p₂
  exact (((IsPlot.dsmooth p₂.2.2).prod_map (IsPlot.dsmooth p₁.2.2)).comp
    toEuclidean.symm.contDiff.dsmooth).continuous.coinduced_le

end Prod

section ULift

variable {X : Type u} [DiffeologicalSpace X]

theorem dsmooth_uLift_down : DSmooth (ULift.down : ULift.{v, u} X → X) :=
  dsmooth_induced_dom

theorem dsmooth_uLift_up : DSmooth (ULift.up : X → ULift.{v, u} X) :=
  dsmooth_induced_rng.2 dsmooth_id

theorem induction_uLift_down : Induction (ULift.down : ULift.{v, u} X → X) :=
  ⟨ULift.down_injective,rfl⟩

-- TODO: ulift discrete diffeologies once instance is available

end ULift

section DSmoothMap

namespace DSmoothMap

variable {X Y Z: Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

/-- The functional diffeology on the space `DSmoothMap X Y` of smooth maps `X → Y`. -/
instance diffeologicalSpace {X Y : Type*} [dX : DiffeologicalSpace X]
    [dY : DiffeologicalSpace Y] : DiffeologicalSpace (DSmoothMap X Y) where
  plots n := {p | DSmooth (Function.uncurry fun x x' => p x x')}
  constant_plots f := f.dsmooth.comp dsmooth_snd
  plot_reparam hp hf := hp.comp <| hf.dsmooth.prod_map dsmooth_id
  locality {n p} h := by
    apply dsmooth_iff_locally_dsmooth.mpr; intro x
    let ⟨u,hu,hxu,h⟩ := h x.1; let _ : TopologicalSpace X := DTop
    refine' ⟨u ×ˢ univ,(hu.prod isOpen_univ).mono dTop_prod_le_prod_dTop,⟨hxu,mem_univ _⟩,_⟩
    intro m f hf; specialize @h m (fun x => (f x).1.1) (fun x => (f x).2.1)
      ((hf.dsmooth.subtype_val.fst).contDiff)
    exact (h.comp (dsmooth_id.prod_mk hf.dsmooth.subtype_val.snd)).isPlot

lemma isPlot_iff {n : ℕ} {p : Eucl n → DSmoothMap X Y} :
    IsPlot p ↔ DSmooth (Function.uncurry fun x y => p x y) := by
  rfl

/-- A map `f : X → DSmoothMap Y Z` is smooth iff the corresponding map `X × Y → Z` is. -/
lemma dsmooth_iff {f : X → DSmoothMap Y Z} :
    DSmooth f ↔ DSmooth (Function.uncurry fun x y => f x y) := by
  refine' ⟨fun hf n p hp => _,fun hf n p hp => hf.comp <| hp.dsmooth.prod_map dsmooth_id⟩
  exact ((hf n _ hp.dsmooth.fst.isPlot).comp <| dsmooth_id.prod_mk hp.dsmooth.snd).isPlot

/-- The evaluation map `DSmoothMap X Y × X → Y` is smooth. -/
lemma dsmooth_eval : DSmooth fun (p : DSmoothMap X Y × X) => p.1 p.2 :=
  fun _ _ hp => ((dsmooth_iff.mp hp.dsmooth.fst).comp <| dsmooth_id.prod_mk hp.dsmooth.snd).isPlot

/-- The composition map `DSmoothMap Y Z × DSmoothMap X Y → DSmoothMap X Z` is smooth. -/
lemma dsmooth_comp : DSmooth fun (x : DSmoothMap Y Z × DSmoothMap X Y) => x.1.comp x.2 := by
  rw [dsmooth_iff]
  refine' dsmooth_eval.comp <| dsmooth_fst.fst.prod_mk _
  exact dsmooth_eval.comp <| dsmooth_snd.prod_map dsmooth_id

/-- The coevaluation map `Y → DSmoothMap X (Y × X)`. -/
def coev (y : Y) : DSmoothMap X (Y × X) :=
  ⟨fun x => (y,x),dsmooth_const.prod_mk dsmooth_id⟩

/-- The coevaluation map is smooth. -/
lemma dsmooth_coev : DSmooth (coev : Y → DSmoothMap X _) :=
  dsmooth_iff.mpr dsmooth_id

/-- The currying map `DSmoothMap (X × Y) Z → DSmoothMap X (DSmoothMap Y Z)` -/
def curry (f : DSmoothMap (X × Y) Z) : DSmoothMap X (DSmoothMap Y Z) :=
  ⟨fun x => ⟨Function.curry f x,f.dsmooth.curry_right⟩,
    (dsmooth_comp.curry_right (x := f)).comp dsmooth_coev⟩

/-- The currying map is smooth. -/
lemma dsmooth_curry : DSmooth (@curry X Y Z _ _ _) :=
  dsmooth_iff.mpr <| dsmooth_iff.mpr <| dsmooth_eval.comp <|
    dsmooth_fst.fst.prod_mk <| dsmooth_fst.snd.prod_mk dsmooth_snd

/-- The uncurrying map `DSmoothMap X (DSmoothMap Y Z) → DSmoothMap (X × Y) Z`. -/
def uncurry (f : DSmoothMap X (DSmoothMap Y Z)) : DSmoothMap (X × Y) Z :=
  ⟨fun x => f x.1 x.2,dsmooth_iff.mp f.dsmooth⟩

/-- The uncurrying map is smooth. -/
lemma dsmooth_uncurry : DSmooth (@uncurry X Y Z _ _ _) :=
  dsmooth_iff.mpr <| dsmooth_eval.comp <|
    (dsmooth_eval.comp <| dsmooth_fst.prod_mk dsmooth_snd.fst).prod_mk dsmooth_snd.snd

end DSmoothMap

end DSmoothMap
