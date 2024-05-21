import Orbifolds.Diffeology.Induced
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Constructions of diffeological spaces
Mostly based on `Mathlib.Topology.Constructions`.
-/

set_option autoImplicit false

open TopologicalSpace Set

open Topology

section Constructions

instance instDiffeologicalSpaceSubtype {X : Type*} [DiffeologicalSpace X] {p : X → Prop} :
    DiffeologicalSpace (Subtype p) :=
  DiffeologicalSpace.induced ((↑) : _ → X) inferInstance

instance instDiffeologicalSpaceProd {X Y : Type*} [dX : DiffeologicalSpace X]
    [dY : DiffeologicalSpace Y] : DiffeologicalSpace (X × Y) :=
  dX.induced Prod.fst ⊓ dY.induced Prod.snd

instance Pi.diffeologicalSpace {ι : Type*} {Y : ι → Type*}
    [(i : ι) → DiffeologicalSpace (Y i)] : DiffeologicalSpace ((i : ι) → Y i) where
  plots n := {p | ∀ i, IsPlot ((fun y => y i) ∘ p)}
  constant_plots _ i := isPlot_const
  plot_reparam {n m p f} := fun hp hf i => by
    exact Function.comp.assoc _ _ _ ▸ isPlot_reparam (hp i) hf
  locality := by sorry

end Constructions

section Pi

variable {ι : Type*} {Y : ι → Type*} [(i : ι) → DiffeologicalSpace (Y i)]
  {X : Type*} [DiffeologicalSpace X] {f : X → ((i : ι) → Y i)}

theorem dsmooth_pi_iff : DSmooth f ↔ ∀ i, DSmooth fun x => f x i := by
  simp only [dsmooth_iff,@forall_comm ι _ _]; rfl

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

theorem dTop_coinduced_comm {X Y : Type*} {dX : DiffeologicalSpace X} {f : X → Y} :
    DTop[dX.coinduced f] = DTop[dX].coinduced f := by
  let dY := dX.coinduced f
  refine' le_antisymm (TopologicalSpace.le_def.2 fun u hu n p hp => _) _
  · rw [isOpen_coinduced] at hu
    dsimp at hp
    sorry
  · exact continuous_iff_coinduced_le.1 <| DSmooth.continuous (by rw [dsmooth_iff_coinduced_le])

theorem isPlot_coinduced_iff {X Y : Type*} {dX : DiffeologicalSpace X} {f : X → Y}
    {n : ℕ} {p : Eucl n → Y} : IsPlot[dX.coinduced f] p ↔ (∃ y, p = fun _ => y) ∨
    ∀ x : Eucl n, ∃ u , IsOpen u ∧ x ∈ u ∧ ∃ p' : u → X, DSmooth p' ∧ p ∘ (↑) = f ∘ p' := by
  sorry

end DTop

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

/-- A product of induced diffeologies is induced by the product map. -/
theorem DiffeologicalSpace.prod_induced_induced (f : X → Y) (g : Z → W) :
    @instDiffeologicalSpaceProd X Z (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) instDiffeologicalSpaceProd := by
  delta instDiffeologicalSpaceProd; simp_rw [induced_inf, induced_compose]; rfl

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

theorem Induction.prod_map {f : X → Y} {g : Z → W} (hf : Induction f) (hg : Induction g) :
    Induction (Prod.map f g) :=
  ⟨hf.1.Prod_map hg.1,by rw [hf.2,hg.2,DiffeologicalSpace.prod_induced_induced f g]; rfl⟩

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

/-- The D-topology of the product diffeology is at least as fine as the product of
  the D-topologies. -/
theorem dTop_prod_le_prod_dTop :
    (DTop : TopologicalSpace (X × Y)) ≤ @instTopologicalSpaceProd _ _ DTop DTop :=
  continuous_id_iff_le.1 ((@continuous_prod_mk _ X Y DTop DTop DTop _ _).2
    ⟨dsmooth_fst.continuous,dsmooth_snd.continuous⟩)

end Prod
