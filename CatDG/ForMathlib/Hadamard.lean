import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hadamard's lemma
Here we prove variants of Hadamard's lemma, stating that a smooth function `f : E → F` between
sufficiently nice vector spaces can for any point `x` and basis `b` be written as
`y ↦ f x + ∑ i, b.repr (y - x) i • g i y` where `b.repr (y - x) i` is the `i`-th component of
`y - x` in the basis `b` and each `g i` is a smooth function `E → F`. We do this by providing
explicit functions `hadamardFun f x (b i)` to serve as the `g i`, characterising their smoothness
and showing that `f` can be written in terms of them.

The functions we consider are specifically functions from finite-dimensional spaces to Banach spaces
that are continuously differentiable on an open star-convex set.

See https://en.wikipedia.org/wiki/Hadamard%27s_lemma and https://ncatlab.org/nlab/show/Hadamard+lemma.
-/

universe u

open ContDiff

variable {E F : Type u} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
  [NormedSpace ℝ F] [CompleteSpace F]

lemma ContinuousOn.intervalIntegral {X : Type*} [TopologicalSpace X] {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.NoAtoms μ] [MeasureTheory.IsLocallyFiniteMeasure μ] {f : X × ℝ → E} {u : Set X}
    {a₀ b₀ : ℝ} (h : a₀ ≤ b₀) (hf : ContinuousOn f (u ×ˢ Set.Icc a₀ b₀)) :
    ContinuousOn (fun x ↦ ∫ t in a₀..b₀, f (x, t) ∂μ) u := by
  rw [continuousOn_iff_continuous_restrict] at hf ⊢
  replace hf :
      Continuous (Function.uncurry fun (x : u) (t : ℝ) ↦ f (x, Set.projIcc _ _ h t)) :=
    (hf.comp (f := (Homeomorph.Set.prod u _).symm ∘ Prod.map id (Set.projIcc _ _ h))
      (by fun_prop)).congr fun (x, t) ↦ by simp
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf a₀ b₀).congr
    fun x ↦ intervalIntegral.integral_congr fun t ht ↦ ?_
  simp [Set.projIcc_of_mem h <| Set.uIcc_of_le h ▸ ht]

open TopologicalSpace MeasureTheory Filter Topology Filter Interval in
/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if `f : H × ℝ → E` is continuously differentiable on `u ×ˢ Ι a b` for a neighbourhood `u` of `x₀`,
then a derivative of `fun x => ∫ t in a..b, f (x, t) ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ`. -/
nonrec theorem intervalIntegral.hasFDerivAt_integral_of_contDiffOn
    {μ : Measure ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℝ E] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {a b : ℝ} {f : H × ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀)
    (hF : ContDiffOn ℝ 1 f (u ×ˢ Set.Icc a b)) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t) ∂μ)
      (∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ) x₀ := by
  sorry

lemma ContDiffOn.intervalIntegral {f : E × ℝ → F} {u : Set E} (hu : IsOpen u) {n : ℕ∞}
    (hf : ContDiffOn ℝ n f (u ×ˢ Set.Icc 0 1)) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in 0..1, f (x, t)) u := by
  revert F; change ∀ F : _, _
  refine ENat.nat_induction n ?_ ?_ ?_
  · intro F _ _ _ f
    simp_rw [WithTop.coe_zero, contDiffOn_zero]
    exact ContinuousOn.intervalIntegral zero_le_one
  · intro k h F _ _ _ f hf
    refine (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := k) hu).2 ⟨?_, by simp, ?_⟩
    · intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := MeasureTheory.volume)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      exact h.differentiableAt.differentiableWithinAt
    · have := hf.fderivWithin (hu.uniqueDiffOn.prod <| uniqueDiffOn_Icc zero_lt_one) (m := k) le_rfl
      refine (h _ (f := fun x ↦ (fderivWithin ℝ f (u ×ˢ Set.Icc 0 1) x).comp (.inl ℝ E ℝ))
        (by fun_prop)).congr ?_
      intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := MeasureTheory.volume)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      rw [h.fderiv]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      rw [show (fun x ↦ f (x, t)) = (f ∘ fun x ↦ (x, t)) by rfl]
      rw [← fderivWithin_eq_fderiv (hu.uniqueDiffWithinAt hx) (((hf.differentiableOn (by simp)).comp
        (by fun_prop) (fun x hx ↦ ⟨hx, ht⟩)).differentiableAt (hu.mem_nhds hx))]
      rw [fderivWithin_comp _ (t := u ×ˢ Set.Icc 0 1) (hf.differentiableOn (by simp) _ ⟨hx, ht⟩)
        (by fun_prop) (fun x hx ↦ ⟨hx, ht⟩) (hu.uniqueDiffWithinAt hx)]
      congr
      exact (hasFDerivAt_prodMk_left x t).hasFDerivWithinAt.fderivWithin (hu.uniqueDiffWithinAt hx)
  · intro h F _ _ _ f hf
    exact contDiffOn_infty.2 fun n ↦ h n F <| hf.of_le <| WithTop.coe_le_coe.2 le_top

/-- The function appearing in Hadamard's lemma applied to the function `f` at `x` for a basis
vector `b`. -/
noncomputable def hadamardFun (f : E → F) (x b : E) : E → F :=
    fun y ↦ ∫ t in (0 : ℝ)..1, lineDeriv ℝ f (x + t • (y - x)) b

protected lemma ContDiffOn.hadamardFun {x : E} {s : Set E} (hs : IsOpen s) (hs' : StarConvex ℝ x s)
    {f : E → F} {n m : ℕ∞} (hf : ContDiffOn ℝ n f s) (hm : m + 1 ≤ n) (b : E) :
    ContDiffOn ℝ m (hadamardFun f x b) s := by
  unfold hadamardFun
  refine ContDiffOn.intervalIntegral (f := fun y ↦ lineDeriv ℝ f (x + y.2 • (y.1 - x)) b) hs ?_
  refine .congr ?_ (fun y hy ↦ DifferentiableAt.lineDeriv_eq_fderiv <|
    (hf.differentiableOn <| by simp [le_of_add_le_right hm]).differentiableAt <|
      hs.mem_nhds <| hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2)
  refine .mono ?_ (s := (fun y : E × ℝ ↦ x + y.2 • (y.1 - x)) ⁻¹' s)
    fun y hy ↦ hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2
  exact (ContinuousLinearMap.apply ℝ F b).contDiff.comp_contDiffOn <|
    (hf.fderiv_of_isOpen hs <| WithTop.coe_le_coe.2 hm).comp (by fun_prop) <| s.mapsTo_preimage _

protected lemma ContDiff.hadamardFun {x : E} {f : E → F} {n m : ℕ∞} (hf : ContDiff ℝ n f)
    (hm : m + 1 ≤ n) (b : E) : ContDiff ℝ m (hadamardFun f x b) :=
  contDiffOn_univ.1 <| (contDiffOn_univ.2 hf).hadamardFun isOpen_univ (starConvex_univ x) hm b

open intervalIntegral in
lemma eqOn_add_sum_hadamardFun {x : E} {s : Set E} (hs : IsOpen s) (hs' : StarConvex ℝ x s)
    {f : E → F} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    s.EqOn f (fun y ↦ f x + ∑ i : ι, b.repr (y - x) i • hadamardFun f x (b i) y) := by
  intro y hy
  have hs'' : ∀ t ∈ Set.uIcc (0 : ℝ) 1, x + t • (y - x) ∈ s := fun t ht ↦ by
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hs'.add_smul_sub_mem hy ht.1 ht.2
  refine sub_eq_iff_eq_add'.1 <| Eq.trans (by simp) <| (integral_deriv_eq_sub
    (a := 0) (b := 1) (f := f ∘ fun t ↦ x + t • (y - x)) ?_ ?_).symm.trans ?_
  · intro t ht
    have := (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht
    fun_prop
  · refine ContinuousOn.intervalIntegrable ?_
    exact ((hf.comp (by fun_prop) <| s.mapsTo_preimage _).continuousOn_deriv_of_isOpen
      (hs.preimage <| by fun_prop) hn).mono fun t ht ↦ hs'' _ ht
  · unfold hadamardFun
    simp_rw [← integral_smul]
    rw [← integral_finset_sum]
    · refine integral_congr fun t ht ↦ ?_
      rw [← fderiv_deriv, fderiv_comp]
      · simp_rw [DifferentiableAt.lineDeriv_eq_fderiv <|
          (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht]
        simp_rw [← ContinuousLinearMap.map_smul, ← map_sum]
        simp [deriv_smul_const, - map_sub]
      · refine (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht
      · simp
    · intro i _
      refine (continuousOn_const.smul ?_).intervalIntegrable
      refine .congr ?_ (fun t ht ↦ DifferentiableAt.lineDeriv_eq_fderiv <|
          (hf.differentiableOn hn).differentiableAt <| hs.mem_nhds <| hs'' _ ht)
      refine .mono ?_  (s := (fun t ↦ x + t • (y - x)) ⁻¹' s) fun t ht ↦ hs'' _ ht
      exact (ContinuousLinearMap.apply ℝ F _).continuous.comp_continuousOn <|
        (hf.continuousOn_fderiv_of_isOpen hs hn).comp (by fun_prop) <| s.mapsTo_preimage _

lemma eq_add_sum_hadamardFun {x : E} {f : E → F} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hn : 1 ≤ n) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    f = (fun y ↦ f x + ∑ i : ι, b.repr (y - x) i • hadamardFun f x (b i) y) := by
  simpa using eqOn_add_sum_hadamardFun isOpen_univ (starConvex_univ x) hf.contDiffOn hn b
