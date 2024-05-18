import Orbifolds.Diffeology.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Induced/coinduced diffeologies and inductions/subductions
In large parts based on `Mathlib.Topology.Order`.
-/

set_option autoImplicit false

section Induced

variable {X Y Z : Type*}

/-- The coarsest diffeology on `X` such that `f : X → Y` is smooth.
Also known as the pullback diffeology. -/
def DiffeologicalSpace.induced (f : X → Y) (dY : DiffeologicalSpace Y) :
    DiffeologicalSpace X where
  plots n := {p | f ∘ p ∈ plots n}
  constant_plots x := constant_plots (f x)
  plot_reparam := isPlot_reparam
  locality {_ p} := locality (p := f ∘ p)

/-- The finest diffeology on `Y` such that `f : X → Y` is smooth.
Also known as the pushforward diffeology. -/
def DiffeologicalSpace.coinduced (f : X → Y) (dX : DiffeologicalSpace X) : DiffeologicalSpace Y :=
  sInf {d | DSmooth[dX,d] f}

variable {dX : DiffeologicalSpace X} {dY : DiffeologicalSpace Y} {dZ : DiffeologicalSpace Z}

theorem isPlot_induced_iff {f : X → Y} {n : ℕ} {p : Eucl n → X} :
    IsPlot[dY.induced f] p ↔ IsPlot[dY] (f ∘ p) := Iff.rfl

theorem DSmooth.le_induced {f : X → Y} (hf : DSmooth[dX,dY] f) : dX ≤ dY.induced f :=
  DiffeologicalSpace.le_def.2 fun ⟨n,p⟩ => hf n p

theorem dsmooth_iff_le_induced {f : X → Y} : DSmooth[dX,dY] f ↔ dX ≤ dY.induced f :=
  ⟨DSmooth.le_induced,DiffeologicalSpace.le_iff.1⟩

theorem DSmooth.coinduced_le {f : X → Y} (hf : DSmooth[dX,dY] f) : dX.coinduced f ≤ dY := by
  exact sInf_le hf

theorem dsmooth_iff_coinduced_le {f : X → Y} : DSmooth[dX,dY] f ↔ dX.coinduced f ≤ dY :=
  ⟨DSmooth.coinduced_le,fun h n p hp => by
    refine' Set.mem_of_mem_of_subset _ <| DiffeologicalSpace.le_iff.1 h n
    exact DiffeologicalSpace.isPlot_sInf_iff.2 fun d hf => hf n p hp⟩

namespace DiffeologicalSpace

theorem coinduced_le_iff_le_induced {f : X → Y} :
    dX.coinduced f ≤ dY ↔ dX ≤ dY.induced f := by
  exact dsmooth_iff_coinduced_le.symm.trans dsmooth_iff_le_induced

theorem gc_coinduced_induced (f : X → Y) :
    GaloisConnection (DiffeologicalSpace.coinduced f) (DiffeologicalSpace.induced f) :=
  fun _ _ => coinduced_le_iff_le_induced

theorem induced_mono {f : X → Y} {d₁ d₂ : DiffeologicalSpace Y} (h : d₁ ≤ d₂) :
    d₁.induced f ≤ d₂.induced f :=
  (gc_coinduced_induced f).monotone_u h

theorem coinduced_mono {f : X → Y} {d₁ d₂ : DiffeologicalSpace X} (h : d₁ ≤ d₂) :
    d₁.coinduced f ≤ d₂.coinduced f :=
  (gc_coinduced_induced f).monotone_l h

@[simp]
theorem induced_top {f : X → Y} : induced f ⊤ = ⊤ :=
  (gc_coinduced_induced f).u_top

@[simp]
theorem induced_inf {d₁ d₂ : DiffeologicalSpace Y} {f : X → Y} :
    (d₁ ⊓ d₂).induced f = d₁.induced f ⊓ d₂.induced f :=
  (gc_coinduced_induced f).u_inf

@[simp]
theorem induced_iInf {ι : Sort*} {d : ι → DiffeologicalSpace Y} {f : X → Y} :
    (⨅ i, d i).induced f = ⨅ i, (d i).induced f :=
  (gc_coinduced_induced f).u_iInf

@[simp]
theorem coinduced_bot {f : X → Y} : coinduced f ⊥ = ⊥ :=
  (gc_coinduced_induced f).l_bot

@[simp]
theorem coinduced_sup {d₁ d₂ : DiffeologicalSpace X} {f : X → Y} :
    (d₁ ⊔ d₂).coinduced f = d₁.coinduced f ⊔ d₂.coinduced f :=
  (gc_coinduced_induced f).l_sup

@[simp]
theorem coinduced_iSup {ι : Sort*} {d : ι → DiffeologicalSpace X} {f : X → Y} :
    (⨆ i, d i).coinduced f = ⨆ i, (d i).coinduced f :=
  (gc_coinduced_induced f).l_iSup

theorem induced_id : dX.induced id = dX :=
  DiffeologicalSpace.ext rfl

theorem induced_compose {f : X → Y} {g : Y → Z} :
    (dZ.induced g).induced f = dZ.induced (g ∘ f) := rfl

/-- TODO: requires explicit characterisation of the indiscrete diffeology. -/
theorem induced_const {y : Y} : (dY.induced fun _ : X => y) = ⊤ := by
  sorry

theorem coinduced_id : dX.coinduced id = dX := by
  simp_rw [coinduced,dsmooth_iff_le_induced,induced_id]
  exact le_antisymm (sInf_le (le_refl dX)) (le_sInf fun d hd => hd)

theorem coinduced_compose {f : X → Y} {g : Y → Z} :
    (dX.coinduced f).coinduced g = dX.coinduced (g ∘ f) := by
  simp_rw [coinduced,dsmooth_iff_le_induced (Y := Z),←induced_compose]
  congr 1; ext d; exact coinduced_le_iff_le_induced

/-- TODO: requires explicit characterisation of the discrete diffeology. -/
theorem coinduced_const {y : Y} : (dX.coinduced fun _ : X => y) = ⊥ := by
  sorry

end DiffeologicalSpace

theorem Equiv.induced_diffeology_symm (e : X ≃ Y) :
    DiffeologicalSpace.induced e.symm = DiffeologicalSpace.coinduced e := by
  refine' funext fun dX => le_antisymm _ _
  · refine' le_sInf fun d hd => (dX.induced_mono hd.le_induced).trans _
    rw [d.induced_compose,self_comp_symm,d.induced_id]
  · rw [dX.coinduced_le_iff_le_induced,dX.induced_compose,symm_comp_self,dX.induced_id]

theorem Equiv.coinduced_diffeology_symm (e : X ≃ Y) :
    DiffeologicalSpace.coinduced e.symm = DiffeologicalSpace.induced e :=
  e.symm.induced_diffeology_symm.symm

/-- TODO: figure out if this is even true. -/
theorem DiffeologicalSpace.induced_generateFrom_eq {g : Set ((n : ℕ) × (Eucl n → Y))} {f : X → Y} :
    (generateFrom g).induced f = generateFrom {⟨n,p⟩ | ⟨n,f ∘ p⟩ ∈ g } := by
  refine' le_antisymm _ _
  · sorry
  · refine' generateFrom_le_iff_subset_toPlots.2 fun ⟨n,p⟩ hp => _
    have h := Set.mem_of_mem_of_subset (Set.mem_setOf_eq ▸ hp) <| self_subset_toPlots_generateFrom g
    exact h

theorem dsmooth_generateFrom_iff {g : Set ((n : ℕ) × (Eucl n → X))} {f : X → Y} :
    DSmooth[DiffeologicalSpace.generateFrom g,dY] f ↔ ∀ n p, ⟨n,p⟩ ∈ g → IsPlot (f ∘ p) := by
  rw [dsmooth_iff_le_induced,DiffeologicalSpace.generateFrom_le_iff_subset_toPlots]
  exact ⟨fun hg n p hp => hg hp,fun hg p hp => hg p.1 p.2 hp⟩

theorem dsmooth_induced_dom {f : X → Y} : DSmooth[dY.induced f,dY] f :=
  dsmooth_iff_le_induced.2 le_rfl

theorem dsmooth_induced_rng {f : X → Y} {g : Z → X} :
    DSmooth[dZ,dY.induced f] g ↔ DSmooth[dZ,dY] (f ∘ g) := by
  simp only [dsmooth_iff_le_induced,DiffeologicalSpace.induced_compose]

theorem dsmooth_coinduced_rng {f : X → Y} :
    DSmooth[dX,dX.coinduced f] f :=
  dsmooth_iff_coinduced_le.2 le_rfl

theorem dsmooth_coinduced_dom {f : X → Y} {g : Y → Z} :
    DSmooth[dX.coinduced f,dZ] g ↔ DSmooth[dX,dZ] (g ∘ f) := by
  simp only [dsmooth_iff_coinduced_le,DiffeologicalSpace.coinduced_compose]

variable {dX' : DiffeologicalSpace X} {dY' : DiffeologicalSpace Y} {f : X → Y}

theorem dsmooth_le_dom (h : dX' ≤ dX) :
    DSmooth[dX,dY] f → DSmooth[dX',dY] f := by
  simp_rw [dsmooth_iff_le_induced]
  exact le_trans h

theorem dsmooth_le_rng (h : dY ≤ dY') :
    DSmooth[dX,dY] f → DSmooth[dX,dY'] f := by
  simp_rw [dsmooth_iff_coinduced_le]
  exact fun h' => le_trans h' h

theorem dsmooth_sup_dom :
    DSmooth[dX ⊔ dX',dY] f ↔ DSmooth[dX,dY] f ∧ DSmooth[dX',dY] f := by
  simp only [dsmooth_iff_le_induced,sup_le_iff]

theorem dsmooth_sup_rng_left :
    DSmooth[dX,dY] f → DSmooth[dX,dY ⊔ dY'] f :=
  dsmooth_le_rng le_sup_left

theorem dsmooth_sup_rng_right :
    DSmooth[dX,dY'] f → DSmooth[dX,dY ⊔ dY'] f :=
  dsmooth_le_rng le_sup_right

theorem dsmooth_sSup_dom {D : Set (DiffeologicalSpace X)} :
    DSmooth[sSup D,dY] f ↔ ∀ d ∈ D, DSmooth[d,dY] f := by
  simp only [dsmooth_iff_le_induced,sSup_le_iff]

theorem dsmooth_sSup_rng {D : Set (DiffeologicalSpace Y)} (h : dY ∈ D) (hf : DSmooth[dX,dY] f) :
    DSmooth[dX,sSup D] f :=
  dsmooth_iff_coinduced_le.2 <| le_sSup_of_le h hf.coinduced_le

theorem dsmooth_iSup_dom {ι : Type*} {D : ι → DiffeologicalSpace X} :
    DSmooth[iSup D,dY] f ↔ ∀ i, DSmooth[D i,dY] f := by
  simp only [dsmooth_iff_le_induced,iSup_le_iff]

theorem dsmooth_iSup_rng {ι : Type*} {D : ι → DiffeologicalSpace Y} {i : ι}
    (h : DSmooth[dX,D i] f) : DSmooth[dX,iSup D] f :=
  dsmooth_sSup_rng ⟨i, rfl⟩ h

theorem dsmooth_inf_rng :
    DSmooth[dX,dY ⊓ dY'] f ↔ DSmooth[dX,dY] f ∧ DSmooth[dX,dY'] f := by
  simp only [dsmooth_iff_coinduced_le,le_inf_iff]

theorem dsmooth_inf_dom_left :
    DSmooth[dX,dY] f → DSmooth[dX ⊓ dX',dY] f :=
  dsmooth_le_dom inf_le_left

theorem dsmooth_inf_dom_right :
    DSmooth[dX',dY] f → DSmooth[dX ⊓ dX',dY] f :=
  dsmooth_le_dom inf_le_right

theorem dsmooth_sInf_dom {D : Set (DiffeologicalSpace X)} (h : dX ∈ D) :
    DSmooth[dX,dY] f → DSmooth[sInf D,dY] f :=
  dsmooth_le_dom <| sInf_le h

theorem dsmooth_sInf_rng {D : Set (DiffeologicalSpace Y)} :
    DSmooth[dX,sInf D] f ↔ ∀ d ∈ D, DSmooth[dX,d] f := by
  simp only [dsmooth_iff_coinduced_le,le_sInf_iff]

theorem dsmooth_iInf_dom {ι : Type*} {D : ι → DiffeologicalSpace X} {i : ι} :
    DSmooth[D i,dY] f → DSmooth[iInf D,dY] f :=
  dsmooth_le_dom <| iInf_le _ _

theorem dsmooth_iInf_rng {ι : Type*} {D : ι → DiffeologicalSpace Y} :
    DSmooth[dX,iInf D] f ↔ ∀ i, DSmooth[dX,D i] f := by
  simp only [dsmooth_iff_coinduced_le, le_iInf_iff]

theorem dsmooth_bot : DSmooth[⊥,dY] f :=
  dsmooth_iff_le_induced.2 bot_le

theorem dsmooth_top : DSmooth[dX,⊤] f :=
  dsmooth_iff_coinduced_le.2 le_top

theorem dsmooth_id_iff_le : DSmooth[dX,dX'] id ↔ dX ≤ dX' := by
  rw [dsmooth_iff_le_induced,dX'.induced_id]

theorem dsmooth_id_of_le (h : dX ≤ dX') : DSmooth[dX,dX'] id :=
  dsmooth_id_iff_le.2 h

end Induced

section Inductions

variable {X Y Z : Type*} [dX : DiffeologicalSpace X] [dY : DiffeologicalSpace Y]
  [dZ : DiffeologicalSpace Z]

@[fun_prop]
def Induction (f : X → Y) : Prop := Function.Injective f ∧ dX = dY.induced f

@[fun_prop]
def Subduction (f : X → Y) : Prop := Function.Surjective f ∧ dY = dX.coinduced f

notation (name := Induction_of) "Induction[" d₁ ", " d₂ "]" => @Induction _ _ d₁ d₂

notation (name := Subduction_of) "Subduction[" d₁ ", " d₂ "]" => @Subduction _ _ d₁ d₂

theorem Function.Injective.induction_induced {dY : DiffeologicalSpace Y} {f : X → Y}
    (hf : Injective f) : Induction[dY.induced f,dY] f :=
  ⟨hf,rfl⟩

theorem Function.Surjective.subduction_coinduced {dX : DiffeologicalSpace X} {f : X → Y}
    (hf : Surjective f) : Subduction[dX,dX.coinduced f] f :=
  ⟨hf,rfl⟩

protected theorem Induction.dsmooth {f : X → Y} (hf : Induction f) : DSmooth f := by
  rw [dsmooth_iff_le_induced,hf.2]

protected theorem Subduction.dsmooth {f : X → Y} (hf : Subduction f) : DSmooth f := by
  rw [dsmooth_iff_coinduced_le,hf.2]

@[fun_prop]
theorem induction_id : Induction (@id X) := ⟨Function.injective_id,(dX.induced_id).symm⟩

theorem Induction.comp {f : X → Y} {g : Y → Z} (hg : Induction g) (hf : Induction f) :
    Induction (g ∘ f) :=
  ⟨hg.1.comp hf.1,by rw [hf.2,hg.2,DiffeologicalSpace.induced_compose]⟩

@[fun_prop]
theorem Induction.comp' {f : X → Y} {g : Y → Z} (hg : Induction g) (hf : Induction f) :
    Induction fun x => g (f x) :=
  Induction.comp hg hf

theorem Induction.of_comp {f : X → Y} {g : Y → Z} (hg : Induction g) (h : Induction (g ∘ f)) :
    Induction f :=
  ⟨h.1.of_comp,hg.2.symm ▸ h.2.trans (dZ.induced_compose).symm⟩

theorem Induction.of_comp_iff {f : X → Y} {g : Y → Z} (hg : Induction g) :
    Induction (g ∘ f) ↔ Induction f :=
  ⟨hg.of_comp,hg.comp⟩

theorem Induction.of_comp' {f : X → Y} {g : Y → Z} (hf : DSmooth f) (hg : DSmooth g)
    (h : Induction (g ∘ f)) : Induction f := by
  refine' ⟨h.1.of_comp,le_antisymm hf.le_induced _⟩
  rw [h.2,←dZ.induced_compose]
  exact dY.induced_mono hg.le_induced

@[fun_prop]
theorem subduction_id : Subduction (@id X) := ⟨Function.surjective_id,(dX.coinduced_id).symm⟩

theorem Subduction.comp {f : X → Y} {g : Y → Z} (hg : Subduction g) (hf : Subduction f) :
    Subduction (g ∘ f) :=
  ⟨hg.1.comp hf.1,by rw [hg.2,hf.2,DiffeologicalSpace.coinduced_compose]⟩

@[fun_prop]
theorem Subduction.comp' {f : X → Y} {g : Y → Z} (hg : Subduction g) (hf : Subduction f) :
    Subduction fun x => g (f x) :=
  Subduction.comp hg hf

theorem Subduction.of_comp {f : X → Y} {g : Y → Z} (hf : Subduction f) (h : Subduction (g ∘ f)) :
    Subduction g :=
  ⟨h.1.of_comp,hf.2.symm ▸ h.2.trans (dX.coinduced_compose).symm⟩

theorem Subduction.of_comp_iff {f : X → Y} {g : Y → Z} (hf : Subduction f) :
    Subduction (g ∘ f) ↔ Subduction g :=
  ⟨hf.of_comp,fun hg => hg.comp hf⟩

theorem Subduction.of_comp' {f : X → Y} {g : Y → Z} (hf : DSmooth f) (hg : DSmooth g)
    (h : Subduction (g ∘ f)) : Subduction g := by
  refine' ⟨h.1.of_comp,le_antisymm _ hg.coinduced_le⟩
  rw [h.2,←dX.coinduced_compose]
  exact DiffeologicalSpace.coinduced_mono hf.coinduced_le

theorem Induction.dsmooth_iff {f : X → Y} {g : Y → Z} (hg : Induction g) :
    DSmooth f ↔ DSmooth (g ∘ f) := by
  refine' ⟨hg.dsmooth.comp,fun h => dsmooth_iff_le_induced.2 _⟩
  rw [hg.2,dZ.induced_compose]; exact h.le_induced

theorem Induction.isPlot_iff {f : X → Y} {n : ℕ} {p : Eucl n → X} (hf : Induction f) :
    IsPlot p ↔ IsPlot (f ∘ p) := by
  rw [isPlot_iff_dsmooth,isPlot_iff_dsmooth,hf.dsmooth_iff]

theorem Subduction.dsmooth_iff {f : X → Y} {g : Y → Z} (hf : Subduction f) :
    DSmooth g ↔ DSmooth (g ∘ f) := by
  refine' ⟨fun hg => hg.comp hf.dsmooth,fun h => dsmooth_iff_coinduced_le.2 _⟩
  rw [hf.2,dX.coinduced_compose]; exact h.coinduced_le

theorem Function.LeftInverse.induction {f : X → Y} {g : Y → X} (h : LeftInverse f g)
    (hf : DSmooth f) (hg : DSmooth g) : Induction g :=
  Induction.of_comp' hg hf (h.comp_eq_id ▸ induction_id)

theorem Function.LeftInverse.subduction {f : X → Y} {g : Y → X} (h : LeftInverse f g)
    (hf : DSmooth f) (hg : DSmooth g) : Subduction f :=
  Subduction.of_comp' hg hf (h.comp_eq_id ▸ subduction_id)

end Inductions
