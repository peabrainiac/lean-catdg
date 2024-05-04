import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.ContDiff.Basic

#check TopologicalSpace.Opens

open TopologicalSpace

class DiffeologicalSpace (X : Type u) extends TopologicalSpace X where
  plots (n : ℕ) : Set ((Fin n → ℝ) → X)
  constant_plots {n : ℕ} (x : X) : (fun _ => x) ∈ plots n
  plot_reparam {n m : ℕ} {p : (Fin m → ℝ) → X} {f : (Fin n → ℝ) → (Fin m → ℝ)} :
    p ∈ plots m → (ContDiff ℝ ⊤ f) → (p ∘ f ∈ plots n)
  isOpen_iff_preimages_plots {u : Set X} :
    TopologicalSpace.IsOpen u ↔ ∀ {n : ℕ}, ∀ p ∈ plots n, TopologicalSpace.IsOpen (p ⁻¹' u)

variable {X Y Z : Type u} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

def IsPlot {n : ℕ} (p : (Fin n → ℝ) → X) : Prop := p ∈ DiffeologicalSpace.plots n

notation (name := IsPlot_of) "IsPlot[" d "]" => @IsPlot _ d

lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen u ↔ ∀ (n : ℕ) (p : (Fin n → ℝ) → X), IsPlot p → IsOpen (p ⁻¹' u) := by exact
  DiffeologicalSpace.isOpen_iff_preimages_plots

@[ext]
protected theorem DiffeologicalSpace.ext {d₁ d₂ : DiffeologicalSpace X}
    (h : IsPlot[d₁] = IsPlot[d₂]) : d₁ = d₂ := by
  cases' d₁ with t₁ p₁ _ _ h₁; cases' d₂ with t₂ p₂ _ _ h₂
  congr 1; ext s
  exact ((show p₁ = p₂ by exact h) ▸ @h₁ s).trans (@h₂ s).symm

def DSmooth (f : X → Y) : Prop := ∀ (n : ℕ) (p : (Fin n → ℝ) → X), IsPlot p → IsPlot (f ∘ p)

protected theorem DSmooth.continuous {f : X → Y} (hf : DSmooth f) : Continuous f := by
  simp_rw [continuous_def,isOpen_iff_preimages_plots]
  exact fun u hu n p hp => hu n (f ∘ p) (hf n p hp)

@[simp] theorem dsmooth_id : DSmooth (@id X) := by simp [DSmooth]

theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp => hg _ _ (hf _ _ hp)

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
