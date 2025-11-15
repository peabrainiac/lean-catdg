import CatDG.Diffeology.Algebra.DSmoothMap
import CatDG.ForMathlib.Hadamard

/-!
# Hadamard's lemma
Here we restate Hadamard's lemma in terms of the API around `DSmoothMap`.

See https://en.wikipedia.org/wiki/Hadamard%27s_lemma and https://ncatlab.org/nlab/show/Hadamard+lemma.
-/

universe u

open ContDiff

variable {E F : Type u} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [DiffeologicalSpace E] [DiffeologicalSpace F]
  [ContDiffCompatible E] [ContDiffCompatible F] [FiniteDimensional ℝ E]

namespace DSmoothMap

/-- The function appearing in Hadamard's lemma applied to the function `f` at `x` for a basis
vector `b`. -/
noncomputable nonrec def hadamardFun (f : DSmoothMap E F) (x b : E) : DSmoothMap E F :=
  ⟨hadamardFun f x b, (f.dsmooth.contDiff.hadamardFun (by simp) x b).dsmooth⟩

-- TODO: move
lemma _root_.ContinuousLinearMap.dsmooth {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] [DiffeologicalSpace E]
    [DiffeologicalSpace F] [ContDiffCompatible E] [ContDiffCompatible F] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] F) : DSmooth f :=
  f.contDiff.dsmooth

-- TODO: move
@[simps!]
def _root_.ContinuousLinearMap.toDSmoothMap {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] [DiffeologicalSpace E]
    [DiffeologicalSpace F] [ContDiffCompatible E] [ContDiffCompatible F] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] F) : DSmoothMap E F :=
  ⟨f, f.dsmooth⟩

variable [CompleteSpace F]

nonrec lemma eq_add_sum_hadamardFun (f : DSmoothMap E F) (x : E) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) :
    f = .const E (f x) + ∑ i : ι, ((b.coord i).toContinuousLinearMap.toDSmoothMap -
      .const E (b.repr x i)) • hadamardFun f x (b i) := by
  have h := eq_add_sum_hadamardFun f.dsmooth.contDiff (by simp) (x := x) b
  refine coe_injective ?_
  convert h
  simp [hadamardFun]

end DSmoothMap
