import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
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

open scoped Interval

variable {E F : Type u} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

lemma ContinuousOn.intervalIntegral {X : Type*} [TopologicalSpace X] {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.NoAtoms μ] [MeasureTheory.IsLocallyFiniteMeasure μ] {f : X × ℝ → E} {u : Set X}
    {a₀ b₀ : ℝ} (hf : ContinuousOn f (u ×ˢ [[a₀, b₀]])) :
    ContinuousOn (fun x ↦ ∫ t in a₀..b₀, f (x, t) ∂μ) u := by
  wlog hab : a₀ ≤ b₀ with h
  · simp_rw [intervalIntegral.integral_symm b₀ a₀]
    exact (h (Set.uIcc_comm a₀ b₀ ▸ hf) (le_of_not_ge hab)).neg
  · rw [Set.uIcc_of_le hab] at hf
    rw [continuousOn_iff_continuous_restrict] at hf ⊢
    replace hf :
        Continuous (Function.uncurry fun (x : u) (t : ℝ) ↦ f (x, Set.projIcc _ _ hab t)) :=
      (hf.comp (f := (Homeomorph.Set.prod u _).symm ∘ Prod.map id (Set.projIcc _ _ hab))
        (by fun_prop)).congr fun (x, t) ↦ by simp
    refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf a₀ b₀).congr
      fun x ↦ intervalIntegral.integral_congr fun t ht ↦ ?_
    simp [Set.projIcc_of_mem hab <| Set.uIcc_of_le hab ▸ ht]

section

open Filter Topology Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The "neighbourhood within" filter for sets. Elements of `𝓝[t] s` are sets containing the
intersection of `t` and a neighbourhood of `s`. -/
def nhdsSetWithin (s t : Set X) : Filter X := 𝓝ˢ s ⊓ 𝓟 t

@[inherit_doc]
scoped[Topology] notation "𝓝ˢ[" t "] " s:100 => nhdsSetWithin s t

@[gcongr, mono]
lemma nhdsSetWithin_mono_left {s s' t : Set X} (h : s ⊆ s') : 𝓝ˢ[t] s ≤ 𝓝ˢ[t] s' :=
  inf_le_inf_right _ <| nhdsSet_mono h

@[gcongr, mono]
lemma nhdsSetWithin_mono_right {s t t' : Set X} (h : t ⊆ t') : 𝓝ˢ[t] s ≤ 𝓝ˢ[t'] s :=
  inf_le_inf_left _ <| principal_mono.2 h

lemma nhdsSetWithin_hasBasis {ι : Sort*} {p : ι → Prop} {s' : ι → Set X} {s : Set X}
    (h : (𝓝ˢ s).HasBasis p s') (t : Set X) : (𝓝ˢ[t] s).HasBasis p fun i => s' i ∩ t :=
  h.inf_principal t

lemma nhdsSetWithin_basis_open (s t : Set X) :
    (𝓝ˢ[t] s).HasBasis (fun u => IsOpen u ∧ s ⊆ u) fun u => u ∩ t :=
  nhdsSetWithin_hasBasis (hasBasis_nhdsSet s) t

lemma mem_nhdsSetWithin {s t u : Set X} : u ∈ 𝓝ˢ[t] s ↔ ∃ v, IsOpen v ∧ s ⊆ v ∧ v ∩ t ⊆ u := by
  simpa [and_assoc] using (nhdsSetWithin_basis_open s t).mem_iff

@[simp]
lemma nhdsSetWithin_singleton {x : X} {s : Set X} : 𝓝ˢ[s] {x} = 𝓝[s] x := by
  simp [nhdsSetWithin, nhdsWithin]

@[simp]
lemma nhdsSetWithin_univ {s : Set X} : 𝓝ˢ[univ] s = 𝓝ˢ s := by
  simp [nhdsSetWithin]

@[simp]
lemma nhdsSetWithin_self {s : Set X} : 𝓝ˢ[s] s = 𝓟 s := by
  simp [nhdsSetWithin, principal_le_nhdsSet]

lemma ContinuousOn.preimage_mem_nhdsSetWithin {f : X → Y} {s : Set X}
    (hf : ContinuousOn f s) {t u t' : Set Y} (h : u ∈ 𝓝ˢ[t'] t) :
    f ⁻¹' u ∈ 𝓝ˢ[s ∩ f ⁻¹' t'] (s ∩ f ⁻¹' t) := by
  have ⟨v, hv⟩ := mem_nhdsSetWithin.1 h
  have ⟨w, hw⟩ := continuousOn_iff'.1 hf v hv.1
  refine mem_nhdsSetWithin.2 ⟨w, hw.1, ?_, ?_⟩
  · exact (inter_comm _ _).trans_subset <| (inter_subset_inter_left _ <| preimage_mono hv.2.1).trans
      (hw.2.trans_subset inter_subset_left)
  · rw [← inter_assoc, ← hw.2, inter_comm _ s, inter_assoc, ← preimage_inter]
    exact inter_subset_right.trans <| preimage_mono hv.2.2

/-- If `f` is continuous on `s` and `u` is a neighbourhood of `t`, then `f ⁻¹' u` is a neighbourhood
of `s ∩ f ⁻¹' t` within `s`. -/
lemma ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet {f : X → Y} {s : Set X}
    (hf : ContinuousOn f s) {t u : Set Y} (h : u ∈ 𝓝ˢ t) : f ⁻¹' u ∈ 𝓝ˢ[s] (s ∩ f ⁻¹' t) := by
  simpa [h] using ContinuousOn.preimage_mem_nhdsSetWithin hf (t := t) (u := u) (t' := univ)

lemma nhdsSetWithin_prod_le {s s' : Set X} {t t' : Set Y} :
    𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) ≤ 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
  simpa [nhdsSetWithin, ← prod_inf_prod] using inf_le_of_left_le <| nhdsSet_prod_le _ _

lemma IsCompact.nhdsSetWithin_prod_eq {s s' : Set X} {t t' : Set Y} (hs : IsCompact s)
    (ht : IsCompact t) : 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t) = 𝓝ˢ[s'] s ×ˢ 𝓝ˢ[t'] t := by
  simp [nhdsSetWithin, ← prod_inf_prod, hs.nhdsSet_prod_eq ht]

end

open Topology Set in
/-- Variant of `generalized_tube_lemma` in terms of `nhdsSetWithin`. -/
lemma generalized_tube_lemma' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s s' : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t) {n : Set (X × Y)}
    (hn : n ∈ 𝓝ˢ[s' ×ˢ t'] (s ×ˢ t)) :
    ∃ u ∈ 𝓝ˢ[s'] s, ∃ v ∈ 𝓝ˢ[t'] t, u ×ˢ v ⊆ n := by
  rwa [hs.nhdsSetWithin_prod_eq ht, Filter.mem_prod_iff] at hn

open Topology Set in
/-- Variant of `generalized_tube_lemma` that only replaces the set in one direction. -/
lemma generalized_tube_lemma_left {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s s' : Set X} (hs : IsCompact s) {t : Set Y} (ht : IsCompact t) {n : Set (X × Y)}
    (hn : n ∈ 𝓝ˢ[s' ×ˢ t] (s ×ˢ t)) :
    ∃ u ∈ 𝓝ˢ[s'] s, u ×ˢ t ⊆ n := by
  rw [hs.nhdsSetWithin_prod_eq ht, nhdsSetWithin_self, Filter.mem_prod_principal] at hn
  exact ⟨_, hn, fun x hx ↦ hx.1 _ hx.2⟩

open Topology Set in
/-- Variant of `generalized_tube_lemma` that only replaces the set in one direction. -/
lemma generalized_tube_lemma_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsCompact s) {t t' : Set Y} (ht : IsCompact t) {n : Set (X × Y)}
    (hn : n ∈ 𝓝ˢ[s ×ˢ t'] (s ×ˢ t)) :
    ∃ u ∈ 𝓝ˢ[t'] t, s ×ˢ u ⊆ n := by
  rw [hs.nhdsSetWithin_prod_eq ht, nhdsSetWithin_self, Filter.mem_prod_iff] at hn
  obtain ⟨s', hs', u, hu, h⟩ := hn
  exact ⟨u, hu, (prod_mono_left hs').trans h⟩

open TopologicalSpace MeasureTheory Filter Topology Interval Set in
/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if `f : H × ℝ → E` is continuously differentiable on `u ×ˢ [[a, b]]` for a neighbourhood `u`
of `x₀`, then a derivative of `fun x => ∫ t in a..b, f (x, t) ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ`. -/
nonrec theorem intervalIntegral.hasFDerivAt_integral_of_contDiffOn
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℝ E] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H × ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {a b : ℝ}
    (hF : ContDiffOn ℝ 1 f (u ×ˢ [[a, b]])) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t) ∂μ)
      (∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ) x₀ := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h (μ := μ) hu (Set.uIcc_comm a b ▸ hF) hab).neg
    · simp [hab, hasFDerivAt_const]
  rw [uIcc_of_le hab.le] at hF
  replace ⟨u, hu, hxu, hF⟩ : ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ContDiffOn ℝ 1 f (u ×ˢ Icc a b) := by
    have ⟨u', hu'⟩ := mem_nhds_iff.1 hu
    exact ⟨u', hu'.2.1, hu'.2.2, hF.mono <| prod_mono_left hu'.1⟩
  let F' := fun x : H × ℝ ↦ fderiv ℝ (fun y ↦ f (y, x.2)) x.1
  have hF' : ContinuousOn F' (u ×ˢ Icc a b) := by
    refine .congr (f := fun x ↦ (fderivWithin ℝ f (u ×ˢ Set.Icc a b) x).comp (.inl ℝ H ℝ))
      ?_ fun x hx ↦ ?_
    · refine ((ContinuousLinearMap.compL ℝ H (H × ℝ) E).flip
        (.inl ℝ H ℝ)).continuous.comp_continuousOn ?_
      refine (hF.continuousOn_fderivWithin ?_ le_rfl)
      exact hu.uniqueDiffOn.prod <| uniqueDiffOn_Icc hab
    · dsimp [F']; rw [show (fun y ↦ f (y, x.2)) = (f ∘ fun y ↦ (y, x.2)) by rfl]
      rw [← fderivWithin_eq_fderiv (s := u) (hu.uniqueDiffWithinAt hx.1) <| by
        refine DifferentiableOn.differentiableAt (s := u) ?_ (hu.mem_nhds hx.1)
        exact ((hF.differentiableOn le_rfl).comp (by fun_prop) (fun y hy ↦ ⟨hy, hx.2⟩))]
      rw [fderivWithin_comp _ (t := u ×ˢ Set.Icc a b) (hF.differentiableOn (by simp) _ ⟨hx.1, hx.2⟩)
        (by fun_prop) (by exact fun y hy ↦ ⟨hy, hx.2⟩) (hu.uniqueDiffWithinAt hx.1)]
      congr
      exact (hasFDerivAt_prodMk_left _ x.2).hasFDerivWithinAt.fderivWithin
        (hu.uniqueDiffWithinAt hx.1)
  let F'' := fun x ↦ ‖F' x‖
  have hF'' : ContinuousOn F'' _ := continuous_norm.comp_continuousOn hF'
  let ⟨ε, hε, hε', B, hB⟩ :
      ∃ ε > 0, Metric.ball x₀ ε ⊆ u ∧ ∃ B, ∀ x ∈ Metric.ball x₀ ε ×ˢ Icc a b, F'' x < B := by
    let ⟨B, hB⟩ := (isCompact_singleton.prod isCompact_Icc).bddAbove_image <|
      hF''.mono <| prod_mono_left <| singleton_subset_iff.2 hxu
    have ⟨v, hv, hv'⟩ := generalized_tube_lemma_left (s := {x₀}) isCompact_singleton
      (t := Icc a b) isCompact_Icc (s' := u) (n := F'' ⁻¹' (Iio (B + 1))) (by
        refine nhdsSetWithin_mono_left ?_ <| hF''.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
          (t := Iic B) (u := Iio (B + 1)) <| isOpen_Iio.mem_nhdsSet.2 (by simp)
        intro x hx
        exact ⟨prod_mono_left (by simp [hxu]) hx, mem_upperBounds.1 hB _ <| mem_image_of_mem _ hx⟩)
    rw [nhdsSetWithin_singleton, hu.nhdsWithin_eq hxu] at hv
    have ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hv (hu.mem_nhds hxu))
    exact ⟨ε, hε, hε'.trans inter_subset_right, B + 1,
      fun x hx ↦ hv' <| prod_mono_left (hε'.trans inter_subset_left) hx⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ B)
    (F' := fun x t ↦ fderiv ℝ (fun x ↦ f (x, t)) x) hε ?_ ?_ ?_ ?_ ?_ ?_
  · refine eventually_nhds_iff.2 ⟨u, fun x hx ↦ ?_, hu, hxu⟩
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine .mono ?_ <| (uIoc_of_le hab.le).trans_le Ioc_subset_Icc_self
    exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hx, ht⟩
  · apply ContinuousOn.intervalIntegrable
    exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hxu, uIcc_of_le hab.le ▸ ht⟩
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine .mono ?_ <| (uIoc_of_le hab.le).trans_le Ioc_subset_Icc_self
    exact hF'.comp (f := fun t ↦ (x₀, t)) (by fun_prop) fun t ht ↦ ⟨hxu, ht⟩
  · refine .of_forall fun t ht x hx ↦ ?_
    exact (hB (x, t) ⟨hx, Ioc_subset_Icc_self <| uIoc_of_le hab.le ▸ ht⟩).le
  · exact intervalIntegrable_const
  · refine .of_forall fun t ht x hx ↦ ?_
    refine (DifferentiableOn.differentiableAt ?_ (hu.mem_nhds <| hε' hx)).hasFDerivAt
    exact hF.differentiableOn_one.comp (by fun_prop) fun x hx ↦
      ⟨hx, Ioc_subset_Icc_self <| uIoc_of_le hab.le ▸ ht⟩

lemma ContDiffOn.intervalIntegral {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsLocallyFiniteMeasure μ] [MeasureTheory.NoAtoms μ]
    {f : E × ℝ → F} {u : Set E} (hu : IsOpen u) {a b : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n f (u ×ˢ [[a, b]])) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in a..b, f (x, t) ∂μ) u := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h hu (Set.uIcc_comm a b ▸ hf) hab).neg
    · simp [hab, contDiffOn_const]
  revert F; change ∀ F : _, _
  refine ENat.nat_induction n ?_ ?_ ?_
  · intro F _ _ f
    simp_rw [WithTop.coe_zero, contDiffOn_zero]
    exact ContinuousOn.intervalIntegral
  · intro k h F _ _ f hf
    refine (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := k) hu).2 ⟨?_, by simp, ?_⟩
    · intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := μ)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      exact h.differentiableAt.differentiableWithinAt
    · have := hf.fderivWithin (hu.uniqueDiffOn.prod <| Set.uIcc_of_le hab.le ▸ uniqueDiffOn_Icc hab)
        (m := k) le_rfl
      refine (h _ (f := fun x ↦ (fderivWithin ℝ f (u ×ˢ [[a, b]]) x).comp (.inl ℝ E ℝ))
        (by fun_prop)).congr ?_
      intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := μ)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      rw [h.fderiv]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [show (fun x ↦ f (x, t)) = (f ∘ fun x ↦ (x, t)) by rfl]
      rw [← fderivWithin_eq_fderiv (hu.uniqueDiffWithinAt hx) (((hf.differentiableOn (by simp)).comp
        (by fun_prop) (fun x hx ↦ ⟨hx, ht⟩)).differentiableAt (hu.mem_nhds hx))]
      rw [fderivWithin_comp _ (t := u ×ˢ [[a, b]]) (hf.differentiableOn (by simp) _ ⟨hx, ht⟩)
        (by fun_prop) (fun x hx ↦ ⟨hx, ht⟩) (hu.uniqueDiffWithinAt hx)]
      congr
      exact (hasFDerivAt_prodMk_left x t).hasFDerivWithinAt.fderivWithin (hu.uniqueDiffWithinAt hx)
  · intro h F _ _ f hf
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
  rw [Set.uIcc_of_le zero_le_one]
  refine .congr ?_ (fun y hy ↦ DifferentiableAt.lineDeriv_eq_fderiv <|
    (hf.differentiableOn <| by simp [le_of_add_le_right hm]).differentiableAt <|
      hs.mem_nhds <| hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2)
  refine .mono ?_ (s := (fun y : E × ℝ ↦ x + y.2 • (y.1 - x)) ⁻¹' s)
    fun y hy ↦ hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2
  exact (ContinuousLinearMap.apply ℝ F b).contDiff.comp_contDiffOn <|
    (hf.fderiv_of_isOpen hs <| WithTop.coe_le_coe.2 hm).comp (by fun_prop) <| s.mapsTo_preimage _

protected lemma ContDiff.hadamardFun {f : E → F} {n m : ℕ∞} (hf : ContDiff ℝ n f)
    (hm : m + 1 ≤ n) (x b : E) : ContDiff ℝ m (hadamardFun f x b) :=
  contDiffOn_univ.1 <| (contDiffOn_univ.2 hf).hadamardFun isOpen_univ (starConvex_univ x) hm b

variable [CompleteSpace F]

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
