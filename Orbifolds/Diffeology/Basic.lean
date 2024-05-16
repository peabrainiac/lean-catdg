import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open TopologicalSpace

open Topology

set_option autoImplicit false

abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A diffeology on `X`, given by the smooth functions (or "plots") from ℝⁿ to `X`. -/
class DiffeologicalSpace (X : Type*) where
  plots (n : ℕ) : Set (Eucl n → X)
  constant_plots {n : ℕ} (x : X) : (fun _ => x) ∈ plots n
  plot_reparam {n m : ℕ} {p : Eucl m → X} {f : Eucl n → Eucl m} :
    p ∈ plots m → (ContDiff ℝ ⊤ f) → (p ∘ f ∈ plots n)
  locality {n : ℕ} {p : Eucl n → X} : (∀ x : Eucl n, ∃ u : Set (Eucl n), x ∈ u ∧ IsOpen u ∧
    ∀ {m : ℕ} {f : Eucl m → Eucl n}, (hfu : ∀ x, f x ∈ u) → ContDiff ℝ ⊤ f → p ∘ f ∈ plots m) →
      p ∈ plots n
  dTopology : TopologicalSpace X := {
    IsOpen := fun u => ∀ {n : ℕ}, ∀ p ∈ plots n, TopologicalSpace.IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ => isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp =>
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp =>
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu => hs u hu p hp
  }
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
      ∀ {n : ℕ}, ∀ p ∈ plots n, TopologicalSpace.IsOpen (p ⁻¹' u) := by rfl

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

/-- D-topoloy of a diffeological space. This is a definition rather than an instance
because the D-topology might not agree with already registered topologies like the one
on normed spaces.-/
def DTop : TopologicalSpace X := DiffeologicalSpace.dTopology

def IsPlot {n : ℕ} (p : Eucl n → X) : Prop := p ∈ DiffeologicalSpace.plots n

/-- A function between diffeological spaces is smooth iff composition with it preserves
smoothness of plots. -/
@[fun_prop]
def DSmooth (f : X → Y) : Prop := ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsPlot (f ∘ p)

notation (name := IsPlot_of) "IsPlot[" d "]" => @IsPlot _ d

notation (name := DSmooth_of) "DSmooth[" d₁ ", " d₂ "]" => @DSmooth _ _ d₁ d₂

end Defs

@[ext]
protected theorem DiffeologicalSpace.ext {d₁ d₂ : DiffeologicalSpace X}
    (h : IsPlot[d₁] = IsPlot[d₂]) : d₁ = d₂ := by
  cases' d₁ with p₁ _ _ _ t₁ h₁; cases' d₂ with p₂ _ _ _ t₂ h₂
  congr 1; ext s
  exact ((show p₁ = p₂ by exact h) ▸ @h₁ s).trans (@h₂ s).symm

lemma isPlot_const {n : ℕ} {x : X} : IsPlot (fun _ => x : Eucl n → X) :=
  DiffeologicalSpace.constant_plots x

lemma isPlot_reparam {n m : ℕ} {p : Eucl m → X} {f : Eucl n → Eucl m}
    (hp : IsPlot p) (hf : ContDiff ℝ ⊤ f) : IsPlot (p ∘ f) :=
  DiffeologicalSpace.plot_reparam hp hf

lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen[DTop] u ↔ ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsOpen (p ⁻¹' u) :=
  DiffeologicalSpace.isOpen_iff_preimages_plots

protected lemma IsPlot.continuous {n : ℕ} {p : Eucl n → X} (hp : IsPlot p) :
    Continuous[_,DTop] p :=
  continuous_def.2 fun _ hu => isOpen_iff_preimages_plots.1 hu n p hp

protected theorem DSmooth.continuous {f : X → Y} (hf : DSmooth f) : Continuous[DTop,DTop] f := by
  simp_rw [continuous_def,isOpen_iff_preimages_plots (X:=X),isOpen_iff_preimages_plots (X:=Y)]
  exact fun u hu n p hp => hu n (f ∘ p) (hf n p hp)

theorem dsmooth_iff {f : X → Y} : DSmooth f ↔
    ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsPlot (f ∘ p) := by rfl

theorem dsmooth_id : DSmooth (@id X) := by simp [DSmooth]

@[fun_prop]
theorem dsmooth_id' : DSmooth fun x : X => x := dsmooth_id

theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp => hg _ _ (hf _ _ hp)

@[fun_prop]
theorem DSmooth.comp' {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (fun x => g (f x)) := hg.comp hf

@[fun_prop]
theorem dsmooth_const {y : Y} : DSmooth fun _ : X => y :=
  fun _ _ _ => isPlot_const

section FiniteDimensionalNormedSpace

#check PartialHomeomorph.univBall

/-- Diffeology on a finite-dimensional normed space. We make this a definition instead of an
instance because we also want to have product diffeologies as an instance, and having both would
cause instance diamonds on spaces like `Fin n → ℝ`. -/
def euclideanDiffeology {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : DiffeologicalSpace X where
  plots _ := {p | ContDiff ℝ ⊤ p}
  constant_plots _ := contDiff_const
  plot_reparam := ContDiff.comp
  locality {n p} := fun hp => by
    refine' contDiff_iff_contDiffAt.2 fun x => _
    let ⟨u,hxu,hu,hu'⟩ := hp x
    let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 hu x hxu
    have h := hu' (f := PartialHomeomorph.univBall x ε) (fun x' => by
      have h := (PartialHomeomorph.univBall x ε).map_source (x := x')
      rw [PartialHomeomorph.univBall_source, PartialHomeomorph.univBall_target x hε] at h
      exact Set.mem_of_mem_of_subset (h (Set.mem_univ _)) hε') PartialHomeomorph.contDiff_univBall
    have h' := h.comp_contDiffOn (PartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine' ContDiffOn.contDiffAt (h'.congr _) (Metric.ball_mem_nhds _ hε)
    rw [Function.comp.assoc,←PartialHomeomorph.coe_trans]
    refine' Set.EqOn.comp_left _
    convert (PartialHomeomorph.symm_trans_self (PartialHomeomorph.univBall x ε)).2.symm
    simp [(PartialHomeomorph.univBall_target x hε)]
  dTopology := inferInstance
  isOpen_iff_preimages_plots := fun {u} => by
    refine' ⟨fun hu _ _ hp => IsOpen.preimage (hp.continuous) hu, fun h => _⟩
    rw [←toEuclidean.preimage_symm_preimage u]
    exact toEuclidean.continuous.isOpen_preimage _ (h _ toEuclidean.symm.contDiff)

/-- Technical condition saying that the diffeology on a space is the one coming from
smoothness in the sense of `ContDiff ℝ ⊤`. Necessary as a hypothesis for some theorems
because some normed spaces carry a diffeology that is equal but not defeq to the normed space
diffeology (for example the product diffeology in the case of `Fin n → ℝ`), so the information
that these theorems still holds needs to be made available via this typeclass. -/
class ContDiffCompatible (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [DiffeologicalSpace X] : Prop where
  isPlot_iff {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ ContDiff ℝ ⊤ p

/-- Technical condition saying that the topology on a type agrees with the D-topology.
Necessary because the D-topologies on for example products and subspaces don't agree with
the product and subspace topologies. -/
class DTopCompatible (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X] : Prop where
  dTop_eq : DTop = t

theorem dTop_eq (X : Type*) [t : TopologicalSpace X] [DiffeologicalSpace X] [DTopCompatible X] :
    DTop = t := DTopCompatible.dTop_eq

/-- A smooth function between spaces that are equipped with the D-topology is continuous. -/
protected theorem DSmooth.continuous' {X Y : Type*} [TopologicalSpace X] [DiffeologicalSpace X]
    [DTopCompatible X] [TopologicalSpace Y] [DiffeologicalSpace Y]
    [DTopCompatible Y] {f : X → Y} (hf : DSmooth f) : Continuous f :=
  dTop_eq X ▸ dTop_eq Y ▸ hf.continuous

instance : DiffeologicalSpace ℝ := euclideanDiffeology

instance : ContDiffCompatible ℝ := ⟨Iff.rfl⟩

instance : DTopCompatible ℝ := ⟨by ext s; rw [isOpen_iff_preimages_plots]⟩

noncomputable instance {ι : Type*} [Fintype ι] : DiffeologicalSpace (EuclideanSpace ℝ ι) :=
  euclideanDiffeology

instance {ι : Type*} [Fintype ι] : ContDiffCompatible (EuclideanSpace ℝ ι) :=
  ⟨Iff.rfl⟩

instance {ι : Type*} [Fintype ι] : DTopCompatible (EuclideanSpace ℝ ι) :=
  ⟨by ext s; rw [isOpen_iff_preimages_plots]⟩

protected theorem IsPlot.dsmooth {n : ℕ} {p : Eucl n → X} (hp : IsPlot p) : DSmooth p :=
  fun _ _ => isPlot_reparam hp

protected theorem DSmooth.isPlot {n : ℕ} {p : Eucl n → X} (hp : DSmooth p) : IsPlot p :=
  hp n id contDiff_id

theorem isPlot_iff_dsmooth {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ DSmooth p :=
  ⟨IsPlot.dsmooth,DSmooth.isPlot⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X]
  [ContDiffCompatible X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [DiffeologicalSpace Y]
  [ContDiffCompatible Y]

theorem isPlot_iff_contDiff {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ ContDiff ℝ ⊤ p :=
  ContDiffCompatible.isPlot_iff

protected theorem ContDiff.dsmooth {f : X → Y} (hf: ContDiff ℝ ⊤ f) : DSmooth f :=
  fun _ _ hp => isPlot_iff_contDiff.2 (hf.comp (isPlot_iff_contDiff.1 hp))

protected theorem DSmooth.contDiff [FiniteDimensional ℝ X] {f : X → Y} (hf : DSmooth f) : ContDiff ℝ ⊤ f := by
  let g := toEuclidean (E := X)
  rw [←Function.comp_id f,←g.symm_comp_self]
  exact (isPlot_iff_contDiff.1 <| hf _ _ (g.symm.contDiff.dsmooth.isPlot)).comp g.contDiff

theorem dsmooth_iff_contDiff [FiniteDimensional ℝ X] {f : X → Y} : DSmooth f ↔ ContDiff ℝ ⊤ f :=
  ⟨DSmooth.contDiff,ContDiff.dsmooth⟩

end FiniteDimensionalNormedSpace

section Reflexive

/-- A diffeological space is called reflexive if the diffeology induced by the
differential structure induced by the diffeology is again the diffeology itself.
Since we don't have differential spaces yet, this is formulated as every function
`p : Eucl n → X` for which all compositions with functions `X → ℝ` are smooth
being a plot. -/
class ReflexiveDiffeologicalSpace (X : Type*) [DiffeologicalSpace X] : Prop where
  isPlot_if : ∀ {n : ℕ} (p : Eucl n → X),
    (∀ f : X → ℝ, DSmooth f → DSmooth (f ∘ p)) → IsPlot p

instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [DiffeologicalSpace X] [ContDiffCompatible X] : ReflexiveDiffeologicalSpace X where
  isPlot_if := fun {n} p hp => by
    let Φ := (toEuclidean (E := X)).trans (EuclideanSpace.equiv _ ℝ)
    refine' isPlot_iff_contDiff.2 <| Φ.comp_contDiff_iff.1 (contDiff_pi.2 fun i => _)
    exact (hp _ (((ContinuousLinearMap.proj i).contDiff).comp Φ.contDiff).dsmooth).contDiff

end Reflexive

section CompleteLattice

instance : LE (DiffeologicalSpace X) where le d₁ d₂ := ∀ n, d₂.plots n ⊆ d₁.plots n

theorem le_def {d₁ d₂ : DiffeologicalSpace X} : d₁ ≤ d₂ ↔ ∀ n, d₂.plots n ⊆ d₁.plots n := by rfl

instance : PartialOrder (DiffeologicalSpace X) where
  le_refl := by simp [le_def,subset_rfl]
  le_trans := fun d₁ d₂ d₃ h₁ h₂ n => (h₂ n).trans (h₁ n)
  le_antisymm := fun d₁ d₂ h₁ h₂ => by
    ext n p; suffices h : p ∈ d₁.plots n ↔ p ∈ d₂.plots n by exact h
    rw [((h₁ n).antisymm (h₂ n)).symm]

-- TODO instance : CompleteLattice (DiffeologicalSpace X) where

end CompleteLattice
