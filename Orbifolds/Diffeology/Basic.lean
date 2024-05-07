import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

open TopologicalSpace

set_option autoImplicit false

class DiffeologicalSpace (X : Type*) extends TopologicalSpace X where
  plots (n : ℕ) : Set ((Fin n → ℝ) → X)
  constant_plots {n : ℕ} (x : X) : (fun _ => x) ∈ plots n
  plot_reparam {n m : ℕ} {p : (Fin m → ℝ) → X} {f : (Fin n → ℝ) → (Fin m → ℝ)} :
    p ∈ plots m → (ContDiff ℝ ⊤ f) → (p ∘ f ∈ plots n)
  isOpen_iff_preimages_plots {u : Set X} :
    TopologicalSpace.IsOpen u ↔ ∀ {n : ℕ}, ∀ p ∈ plots n, TopologicalSpace.IsOpen (p ⁻¹' u)

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

def IsPlot {n : ℕ} (p : (Fin n → ℝ) → X) : Prop := p ∈ DiffeologicalSpace.plots n

def DSmooth (f : X → Y) : Prop := ∀ (n : ℕ) (p : (Fin n → ℝ) → X), IsPlot p → IsPlot (f ∘ p)

notation (name := IsPlot_of) "IsPlot[" d "]" => @IsPlot _ d

notation (name := DSmooth_of) "DSmooth[" d₁ ", " d₂ "]" => @DSmooth _ _ d₁ d₂

end Defs

lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen u ↔ ∀ (n : ℕ) (p : (Fin n → ℝ) → X), IsPlot p → IsOpen (p ⁻¹' u) := by exact
  DiffeologicalSpace.isOpen_iff_preimages_plots

@[ext]
protected theorem DiffeologicalSpace.ext {d₁ d₂ : DiffeologicalSpace X}
    (h : IsPlot[d₁] = IsPlot[d₂]) : d₁ = d₂ := by
  cases' d₁ with t₁ p₁ _ _ h₁; cases' d₂ with t₂ p₂ _ _ h₂
  congr 1; ext s
  exact ((show p₁ = p₂ by exact h) ▸ @h₁ s).trans (@h₂ s).symm

protected theorem DSmooth.continuous {f : X → Y} (hf : DSmooth f) : Continuous f := by
  simp_rw [continuous_def,isOpen_iff_preimages_plots (X:=X),isOpen_iff_preimages_plots (X:=Y)]
  exact fun u hu n p hp => hu n (f ∘ p) (hf n p hp)

@[simp] theorem dsmooth_id : DSmooth (@id X) := by simp [DSmooth]

theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp => hg _ _ (hf _ _ hp)

section FiniteDimensionalNormedSpace

/-- A choice of linear homeomorphism from `X` to some `Fin n → ℝ`.
TODO: generalise and move to other file. -/
noncomputable def FiniteDimensional.continuousLinearEquiv_finrank_pi (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    X ≃L[ℝ] Fin (FiniteDimensional.finrank ℝ X) → ℝ :=
  (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp)).some

instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    DiffeologicalSpace X where
  plots _ := {p | ContDiff ℝ ⊤ p}
  constant_plots _ := contDiff_const
  plot_reparam := ContDiff.comp
  isOpen_iff_preimages_plots := by
    refine' fun {u} => ⟨fun hu _ _ hp => IsOpen.preimage (hp.continuous) hu, fun h => _⟩
    let f := FiniteDimensional.continuousLinearEquiv_finrank_pi X
    rw [←f.preimage_symm_preimage u]
    exact f.continuous.isOpen_preimage _ (h _ f.symm.contDiff)

theorem dsmooth_iff_isPlot {n : ℕ} {p : (Fin n → ℝ) → X} : DSmooth p ↔ IsPlot p := by
  rw [DSmooth]
  exact ⟨fun h => h n id contDiff_id,fun hp n f hf => DiffeologicalSpace.plot_reparam hp hf⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

protected theorem ContDiff.dsmooth {f : X → Y} (hf: ContDiff ℝ ⊤ f) : DSmooth f :=
  fun _ _ hp => hf.comp hp

protected theorem DSmooth.contDiff {f : X → Y} (hf : DSmooth f) : ContDiff ℝ ⊤ f := by
  let g := FiniteDimensional.continuousLinearEquiv_finrank_pi X
  rw [←Function.comp_id f,←g.symm_comp_self]
  exact (hf _ _ (dsmooth_iff_isPlot.1 g.symm.contDiff.dsmooth)).comp g.contDiff

theorem dsmooth_iff_contDiff {f : X → Y} : DSmooth f ↔ ContDiff ℝ ⊤ f :=
  ⟨DSmooth.contDiff,ContDiff.dsmooth⟩

end FiniteDimensionalNormedSpace

section Reflexive

/-- A diffeological space is called reflexive if the diffeology induced by the
differential structure induced by the diffeology is again the diffeology itself.
Since we don't have differential spaces yet, this is formulated as every function
`p : (Fin n → ℝ) → X` for which all compositions with functions `X → ℝ` are smooth
being a plot. -/
class ReflexiveDiffeologicalSpace (X : Type*) [DiffeologicalSpace X] : Prop where
  isPlot_if : ∀ {n : ℕ} (p : (Fin n → ℝ) → X),
    (∀ f : X → ℝ, DSmooth f → DSmooth (f ∘ p)) → IsPlot p

instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    ReflexiveDiffeologicalSpace X where
  isPlot_if := fun {n} p hp => by
    let Φ := FiniteDimensional.continuousLinearEquiv_finrank_pi X
    refine' Φ.comp_contDiff_iff.1 (contDiff_pi.2 fun i => _)
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
