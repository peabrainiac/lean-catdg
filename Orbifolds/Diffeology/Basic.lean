import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.LocallyConstant.Basic

open TopologicalSpace

open Topology ContDiff

abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A diffeology on `X`, given by the smooth functions (or "plots") from ℝⁿ to `X`. -/
class DiffeologicalSpace (X : Type*) where
  plots (n : ℕ) : Set (Eucl n → X)
  constant_plots {n : ℕ} (x : X) : (fun _ ↦ x) ∈ plots n
  plot_reparam {n m : ℕ} {p : Eucl m → X} {f : Eucl n → Eucl m} :
    p ∈ plots m → (ContDiff ℝ ∞ f) → (p ∘ f ∈ plots n)
  -- TODO this is currently a little awkward, since it can't be stated in terms of smooth maps
  --      like it should. Adding prediffeologies as an intermediate construction might be smart.
  locality {n : ℕ} {p : Eucl n → X} : (∀ x : Eucl n, ∃ u : Set (Eucl n), IsOpen u ∧ x ∈ u ∧
    ∀ {m : ℕ} {f : Eucl m → Eucl n}, (hfu : ∀ x, f x ∈ u) → ContDiff ℝ ∞ f → p ∘ f ∈ plots m) →
      p ∈ plots n
  dTopology : TopologicalSpace X := {
    IsOpen := fun u ↦ ∀ {n : ℕ}, ∀ p ∈ plots n, TopologicalSpace.IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp
  }
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
      ∀ {n : ℕ}, ∀ p ∈ plots n, TopologicalSpace.IsOpen (p ⁻¹' u) := by rfl

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

section Defs

/-- D-topology of a diffeological space. This is a definition rather than an instance
because the D-topology might not agree with already registered topologies like the one
on normed spaces.-/
def DTop : TopologicalSpace X := DiffeologicalSpace.dTopology

def IsPlot {n : ℕ} (p : Eucl n → X) : Prop := p ∈ DiffeologicalSpace.plots n

/-- A function between diffeological spaces is smooth iff composition with it preserves
smoothness of plots. -/
@[fun_prop]
def DSmooth (f : X → Y) : Prop := ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsPlot (f ∘ p)

notation (name := DTop_of) "DTop[" d "]" => @DTop _ d

notation (name := IsPlot_of) "IsPlot[" d "]" => @IsPlot _ d

notation (name := DSmooth_of) "DSmooth[" d₁ ", " d₂ "]" => @DSmooth _ _ d₁ d₂

end Defs

omit [DiffeologicalSpace X] in
@[ext]
protected theorem DiffeologicalSpace.ext {d₁ d₂ : DiffeologicalSpace X}
    (h : IsPlot[d₁] = IsPlot[d₂]) : d₁ = d₂ := by
  cases' d₁ with p₁ _ _ _ t₁ h₁; cases' d₂ with p₂ _ _ _ t₂ h₂
  congr 1; ext s
  exact ((show p₁ = p₂ by exact h) ▸ @h₁ s).trans (@h₂ s).symm

lemma isPlot_const {n : ℕ} {x : X} : IsPlot (fun _ ↦ x : Eucl n → X) :=
  DiffeologicalSpace.constant_plots x

lemma isPlot_reparam {n m : ℕ} {p : Eucl m → X} {f : Eucl n → Eucl m}
    (hp : IsPlot p) (hf : ContDiff ℝ ∞ f) : IsPlot (p ∘ f) :=
  DiffeologicalSpace.plot_reparam hp hf

lemma isOpen_iff_preimages_plots {u : Set X} :
    IsOpen[DTop] u ↔ ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsOpen (p ⁻¹' u) :=
  DiffeologicalSpace.isOpen_iff_preimages_plots

protected lemma IsPlot.continuous {n : ℕ} {p : Eucl n → X} (hp : IsPlot p) :
    Continuous[_,DTop] p :=
  continuous_def.2 fun _ hu ↦ isOpen_iff_preimages_plots.1 hu n p hp

protected theorem DSmooth.continuous {f : X → Y} (hf : DSmooth f) : Continuous[DTop,DTop] f := by
  simp_rw [continuous_def,isOpen_iff_preimages_plots (X:=X),isOpen_iff_preimages_plots (X:=Y)]
  exact fun u hu n p hp ↦ hu n (f ∘ p) (hf n p hp)

theorem dsmooth_iff {f : X → Y} : DSmooth f ↔
    ∀ (n : ℕ) (p : Eucl n → X), IsPlot p → IsPlot (f ∘ p) := by rfl

theorem dsmooth_id : DSmooth (@id X) := by simp [DSmooth]

@[fun_prop]
theorem dsmooth_id' : DSmooth fun x : X ↦ x := dsmooth_id

theorem DSmooth.comp {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (g ∘ f) :=
  fun _ _ hp ↦ hg _ _ (hf _ _ hp)

@[fun_prop]
theorem DSmooth.comp' {f : X → Y} {g : Y → Z} (hg : DSmooth g) (hf : DSmooth f) :
    DSmooth (fun x ↦ g (f x)) := hg.comp hf

@[fun_prop]
theorem dsmooth_const {y : Y} : DSmooth fun _ : X ↦ y :=
  fun _ _ _ ↦ isPlot_const

/-- Replaces the D-topology of a diffeology with another topology equal to it. Useful
to construct diffeologies with better definitional equalities. -/
def DiffeologicalSpace.withDTopology {X : Type*} (d : DiffeologicalSpace X)
    (t : TopologicalSpace X) (h : DTop[d] = t) : DiffeologicalSpace X where
  dTopology := t
  isOpen_iff_preimages_plots := by intro _; rw [← d.isOpen_iff_preimages_plots, ← h]
  __ := d

lemma DiffeologicalSpace.withDTopology_eq {X : Type*} {d : DiffeologicalSpace X}
    {t : TopologicalSpace X} {h : DTop[d] = t} : d.withDTopology t h = d := by
  ext; rfl

/-- A structure with plots specified on open subsets of ℝⁿ rather than ℝⁿ itself. Useful
for constructing diffeologies, as it often makes the locality condition easiert to prove. -/
structure DiffeologicalSpace.CorePlotsOn (X : Type*) where
  isPlotOn {n : ℕ} {u : Set (Eucl n)} (hu : IsOpen u) : (Eucl n → X) → Prop
  isPlotOn_congr {n : ℕ} {u : Set (Eucl n)} (hu : IsOpen u) {p q : Eucl n → X}
    (h : Set.EqOn p q u) : isPlotOn hu p ↔ isPlotOn hu q
  /-- The predicate that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  isPlot {n : ℕ} : (Eucl n → X) → Prop := fun p ↦ isPlotOn isOpen_univ p
  isPlotOn_univ {n : ℕ} {p : Eucl n → X} : isPlotOn isOpen_univ p ↔ isPlot p := by simp
  isPlot_const {n : ℕ} (x : X) : isPlot fun (_ : Eucl n) ↦ x
  isPlotOn_reparam {n m : ℕ} {u : Set (Eucl n)} {v : Set (Eucl m)} {hu : IsOpen u}
    (hv : IsOpen v) {p : Eucl n → X} {f : Eucl m → Eucl n} (h : Set.MapsTo f v u) :
    isPlotOn hu p → ContDiffOn ℝ ∞ f v → isPlotOn hv (p ∘ f)
  /-- The locality axiom of diffeologies, phrased in terms of `isPlotOn`. -/
  locality {n : ℕ} {u : Set (Eucl n)} (hu : IsOpen u) {p : Eucl n → X} :
    (∀ x ∈ u, ∃ (v : Set (Eucl n)) (hv : IsOpen v), x ∈ v ∧ isPlotOn hv p) → isPlotOn hu p
  /-- The D-topology that the diffeology built from this structure will use. Can be overwritten
  to allow for better definitional equalities. -/
  dTopology : TopologicalSpace X := {
    IsOpen := fun u ↦ ∀ {n : ℕ}, ∀ p : Eucl n → X, isPlot p → TopologicalSpace.IsOpen (p ⁻¹' u)
    isOpen_univ := fun _ _ ↦ isOpen_univ
    isOpen_inter := fun _ _ hs ht _ p hp ↦
      Set.preimage_inter.symm ▸ (IsOpen.inter (hs p hp) (ht p hp))
    isOpen_sUnion := fun _ hs _ p hp ↦
      Set.preimage_sUnion ▸ isOpen_biUnion fun u hu ↦ hs u hu p hp
  }
  isOpen_iff_preimages_plots {u : Set X} : dTopology.IsOpen u ↔
    ∀ {n : ℕ}, ∀ p : Eucl n → X, isPlot p → TopologicalSpace.IsOpen (p ⁻¹' u) := by rfl

/-- Constructs a diffeology from plots defined on open subsets or ℝⁿ rather than ℝⁿ itself,
organised in the form of the auxiliary `CorePlotsOn` structure.
This is more involved in most regards, but also often makes it quite a lot easier to prove
the locality condition. -/
def DiffeologicalSpace.mkOfPlotsOn {X : Type*} (d : CorePlotsOn X) : DiffeologicalSpace X where
  plots _ := {p | d.isPlot p}
  constant_plots _ := d.isPlot_const _
  plot_reparam hp hf := d.isPlotOn_univ.mp <|
    d.isPlotOn_reparam _ (Set.mapsTo_univ _ _) (d.isPlotOn_univ.mpr hp) hf.contDiffOn
  locality {n p} h := by
    dsimp at h
    refine d.isPlotOn_univ.mp <| d.locality _ fun x _ ↦ ?_
    let ⟨u,hu,hxu,hu'⟩ := h x
    let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.mp hu x hxu
    have h := hu' (f := PartialHomeomorph.univBall x ε) (fun x' ↦ by
      have h := (PartialHomeomorph.univBall x ε).map_source (x := x')
      rw [PartialHomeomorph.univBall_source, PartialHomeomorph.univBall_target x hε] at h
      exact hε' (h (Set.mem_univ _))) PartialHomeomorph.contDiff_univBall
    have h' := d.isPlotOn_reparam (Metric.isOpen_ball) (Set.mapsTo_univ _ _)
      (d.isPlotOn_univ.mpr h) (PartialHomeomorph.contDiffOn_univBall_symm (c := x) (r := ε))
    refine ⟨_,Metric.isOpen_ball,Metric.mem_ball_self hε,(d.isPlotOn_congr _ ?_).mp h'⟩
    rw [Function.comp_assoc,←PartialHomeomorph.coe_trans]; apply Set.EqOn.comp_left
    convert (PartialHomeomorph.symm_trans_self (PartialHomeomorph.univBall x ε)).2
    simp [(PartialHomeomorph.univBall_target x hε)]
  dTopology := d.dTopology
  isOpen_iff_preimages_plots := d.isOpen_iff_preimages_plots

section FiniteDimensionalNormedSpace

/-- Diffeology on a finite-dimensional normed space. We make this a definition instead of an
instance because we also want to have product diffeologies as an instance, and having both would
cause instance diamonds on spaces like `Fin n → ℝ`. -/
def euclideanDiffeology {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : DiffeologicalSpace X :=
  DiffeologicalSpace.mkOfPlotsOn {
    isPlotOn := fun {_ u} _ p ↦ ContDiffOn ℝ ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contDiffOn_congr h
    isPlot := fun p ↦ ContDiff ℝ ∞ p
    isPlotOn_univ := contDiffOn_univ
    isPlot_const := fun _ ↦ contDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf h.subset_preimage
    locality := fun _ _ h ↦ fun x hxu ↦ by
      let ⟨v,hv,hxv,hv'⟩ := h x hxu
      exact ((hv' x hxv).contDiffAt (hv.mem_nhds hxv)).contDiffWithinAt
    dTopology := inferInstance
    isOpen_iff_preimages_plots := fun {u} ↦ by
      refine ⟨fun hu _ _ hp ↦ IsOpen.preimage (hp.continuous) hu, fun h ↦ ?_⟩
      rw [←toEuclidean.preimage_symm_preimage u]
      exact toEuclidean.continuous.isOpen_preimage _ (h _ toEuclidean.symm.contDiff) }

/-- Technical condition saying that the diffeology on a space is the one coming from
smoothness in the sense of `ContDiff ℝ ∞`. Necessary as a hypothesis for some theorems
because some normed spaces carry a diffeology that is equal but not defeq to the normed space
diffeology (for example the product diffeology in the case of `Fin n → ℝ`), so the information
that these theorems still holds needs to be made available via this typeclass. -/
class ContDiffCompatible (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [DiffeologicalSpace X] : Prop where
  isPlot_iff {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ ContDiff ℝ ∞ p

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

instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : @ContDiffCompatible X _ _ euclideanDiffeology :=
  let _ := euclideanDiffeology (X := X); ⟨Iff.rfl⟩

lemma contDiffCompatible_iff_eq_euclideanDiffeology {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [d : DiffeologicalSpace X] :
    ContDiffCompatible X ↔ d = euclideanDiffeology :=
  ⟨fun _ ↦ by ext n p; exact ContDiffCompatible.isPlot_iff, fun h ↦ h ▸ inferInstance⟩

instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : @DTopCompatible X _ euclideanDiffeology :=
  let _ := euclideanDiffeology (X := X); ⟨rfl⟩

noncomputable instance : DiffeologicalSpace ℝ := euclideanDiffeology

example : ContDiffCompatible ℝ := inferInstance

example : DTopCompatible ℝ := inferInstance

noncomputable instance : DiffeologicalSpace ℂ := euclideanDiffeology

example : ContDiffCompatible ℂ := inferInstance

example : DTopCompatible ℂ := inferInstance

noncomputable instance {ι : Type*} [Fintype ι] : DiffeologicalSpace (EuclideanSpace ℝ ι) :=
  euclideanDiffeology

example {ι : Type*} [Fintype ι] : ContDiffCompatible (EuclideanSpace ℝ ι) := inferInstance

example {ι : Type*} [Fintype ι] : DTopCompatible (EuclideanSpace ℝ ι) := inferInstance

protected theorem IsPlot.dsmooth {n : ℕ} {p : Eucl n → X} (hp : IsPlot p) : DSmooth p :=
  fun _ _ ↦ isPlot_reparam hp

protected theorem DSmooth.isPlot {n : ℕ} {p : Eucl n → X} (hp : DSmooth p) : IsPlot p :=
  hp n id <| @contDiff_id ℝ _ (Eucl n) _ _ ∞

theorem isPlot_iff_dsmooth {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ DSmooth p :=
  ⟨IsPlot.dsmooth,DSmooth.isPlot⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X]
  [ContDiffCompatible X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [DiffeologicalSpace Y]
  [ContDiffCompatible Y]

theorem isPlot_iff_contDiff {n : ℕ} {p : Eucl n → X} : IsPlot p ↔ ContDiff ℝ ∞ p :=
  ContDiffCompatible.isPlot_iff

protected theorem ContDiff.dsmooth {f : X → Y} (hf: ContDiff ℝ ∞ f) : DSmooth f :=
  fun _ _ hp ↦ isPlot_iff_contDiff.2 (hf.comp (isPlot_iff_contDiff.1 hp))

protected theorem DSmooth.contDiff [FiniteDimensional ℝ X] {f : X → Y} (hf : DSmooth f) :
    ContDiff ℝ ∞ f := by
  let g := toEuclidean (E := X)
  rw [←Function.comp_id f,←g.symm_comp_self]
  exact (isPlot_iff_contDiff.1 <| hf _ _ (g.symm.contDiff.dsmooth.isPlot)).comp g.contDiff

theorem dsmooth_iff_contDiff [FiniteDimensional ℝ X] {f : X → Y} : DSmooth f ↔ ContDiff ℝ ∞ f :=
  ⟨DSmooth.contDiff,ContDiff.dsmooth⟩

end FiniteDimensionalNormedSpace

section CompleteLattice

namespace DiffeologicalSpace

variable {X : Type*}

/-- The plots belonging to a diffeology, as a subset of `(n : ℕ) × (Eucl n → X)`. -/
def toPlots (_ : DiffeologicalSpace X) : Set ((n : ℕ) × (Eucl n → X)) :=
  {p | IsPlot p.2}

lemma injective_toPlots : Function.Injective (@toPlots X) := fun d d' h ↦ by
  ext n p; exact Set.ext_iff.1 h ⟨n,p⟩

/-- The plots belonging to the diffeology generated by `g`. -/
def generatePlots (g : Set ((n : ℕ) × (Eucl n → X))) : Set ((n : ℕ) × (Eucl n → X)) :=
  ⋂ d ∈ {d : DiffeologicalSpace X | g ⊆ d.toPlots}, d.toPlots

/-- The diffeology generated by a set `g` of plots. -/
def generateFrom (g : Set ((n : ℕ) × (Eucl n → X))) : DiffeologicalSpace X where
  plots n := {p | ⟨n,p⟩ ∈ generatePlots g}
  constant_plots {n} x := Set.mem_iInter₂.2 fun _ _ ↦ constant_plots x
  plot_reparam {n m p f} := fun hp hf ↦ Set.mem_iInter₂.2 fun d hd ↦
    @plot_reparam X d n m p f (Set.mem_iInter₂.1 hp _ hd) hf
  locality {n p} := fun hp ↦ Set.mem_iInter₂.2 fun d hd ↦ @locality X d n p fun x ↦ by
    let ⟨u,hxu,hu,hu'⟩ := hp x
    exact ⟨u,hxu,hu,fun {m f} hfu hf ↦ Set.mem_iInter₂.1 (hu' hfu hf) _ hd⟩

lemma self_subset_toPlots_generateFrom (g : Set ((n : ℕ) × (Eucl n → X))) :
    g ⊆ (generateFrom g).toPlots :=
  Set.subset_iInter₂ fun _ hd ↦ hd

lemma isPlot_generateFrom_of_mem {g : Set ((n : ℕ) × (Eucl n → X))} {n : ℕ} {p : Eucl n → X}
    (hp : ⟨n, p⟩ ∈ g) : IsPlot[generateFrom g] p :=
  self_subset_toPlots_generateFrom g hp

instance : PartialOrder (DiffeologicalSpace X) := PartialOrder.lift _ injective_toPlots

lemma le_def {d₁ d₂ : DiffeologicalSpace X} : d₁ ≤ d₂ ↔ d₁.toPlots ⊆ d₂.toPlots := by rfl

lemma le_iff {d₁ d₂ : DiffeologicalSpace X} : d₁ ≤ d₂ ↔ ∀ n, d₁.plots n ⊆ d₂.plots n :=
  le_def.trans ⟨fun h n p h' ↦ (h h' : ⟨n,p⟩ ∈ d₂.toPlots),fun h _ hp ↦ h _ hp⟩

lemma le_iff' {d₁ d₂ : DiffeologicalSpace X} : d₁ ≤ d₂ ↔
    ∀ n (p : Eucl n → X), IsPlot[d₁] p → IsPlot[d₂] p := le_iff

lemma generateFrom_le_iff_subset_toPlots {g : Set ((n : ℕ) × (Eucl n → X))}
    {d : DiffeologicalSpace X} : generateFrom g ≤ d ↔ g ⊆ d.toPlots :=
  ⟨fun h ↦ (self_subset_toPlots_generateFrom g).trans h,fun h ↦ le_def.2 (Set.iInter₂_subset d h)⟩

/-- Version of `generateFrom_le_iff_subset_toPlots` that is stated in terms of `IsPlot` instead
of `toPlots`. -/
lemma generateFrom_le_iff {g : Set ((n : ℕ) × (Eucl n → X))} {d : DiffeologicalSpace X} :
    generateFrom g ≤ d ↔ ∀ n (p : Eucl n → X), ⟨n, p⟩ ∈ g → IsPlot[d] p :=
  generateFrom_le_iff_subset_toPlots.trans ⟨fun h _ _ hp ↦ h hp, fun h _ hp ↦ h _ _ hp⟩

/-- The diffeology defined by `g`. Same as `generateFrom g`, except that its set of plots is
definitionally equal to `g`. -/
protected def mkOfClosure (g : Set ((n : ℕ) × (Eucl n → X))) (hg : (generateFrom g).toPlots = g) :
    DiffeologicalSpace X where
  plots n := {p | ⟨n,p⟩ ∈ g}
  constant_plots := hg ▸ (generateFrom g).constant_plots
  plot_reparam := hg ▸ (generateFrom g).plot_reparam
  locality := hg ▸ (generateFrom g).locality

lemma mkOfClosure_eq_generateFrom {g : Set ((n : ℕ) × (Eucl n → X))}
    {hg : (generateFrom g).toPlots = g} : DiffeologicalSpace.mkOfClosure g hg = generateFrom g :=
  injective_toPlots hg.symm

theorem gc_generateFrom (X : Type*) : GaloisConnection generateFrom (@toPlots X) :=
  @generateFrom_le_iff_subset_toPlots X

/-- The Galois insertion between `DiffeologicalSpace α` and `Set ((n : ℕ) × (Eucl n → X))` whose
lower part sends a collection of plots in `X` to the diffeology they generate, and whose upper
part sends a diffeology to its collection of plots. -/
def giGenerateFrom (X : Type*) : GaloisInsertion generateFrom (@toPlots X) where
  gc := gc_generateFrom X
  le_l_u := fun _ ↦ le_def.2 (self_subset_toPlots_generateFrom _)
  choice g hg := DiffeologicalSpace.mkOfClosure g (hg.antisymm (self_subset_toPlots_generateFrom g))
  choice_eq _ _ := mkOfClosure_eq_generateFrom

instance : CompleteLattice (DiffeologicalSpace X) := (giGenerateFrom X).liftCompleteLattice

@[mono]
theorem generateFrom_mono {g₁ g₂ : Set ((n : ℕ) × (Eucl n → X))} (h : g₁ ⊆ g₂) :
    generateFrom g₁ ≤ generateFrom g₂ :=
  (gc_generateFrom _).monotone_l h

theorem generateFrom_toPlots (d : DiffeologicalSpace X) :
    generateFrom d.toPlots = d :=
  (giGenerateFrom X).l_u_eq d

theorem leftInverse_generateFrom :
    Function.LeftInverse generateFrom (@toPlots X) :=
  (giGenerateFrom X).leftInverse_l_u

theorem generateFrom_surjective : Function.Surjective (@generateFrom X) :=
  (giGenerateFrom X).l_surjective

theorem generateFrom_union (g₁ g₂ : Set ((n : ℕ) × (Eucl n → X))) :
    generateFrom (g₁ ∪ g₂) = generateFrom g₁ ⊔ generateFrom g₂ :=
  (gc_generateFrom X).l_sup

theorem generateFrom_iUnion {ι : Type*} {g : ι → Set ((n : ℕ) × (Eucl n → X))} :
    generateFrom (⋃ i, g i) = ⨆ i, generateFrom (g i) :=
  (gc_generateFrom X).l_iSup

theorem generateFrom_sUnion {G : Set (Set ((n : ℕ) × (Eucl n → X)))} :
    generateFrom (⋃₀ G) = ⨆ s ∈ G, generateFrom s :=
  (gc_generateFrom X).l_sSup

theorem toPlots_inf (d₁ d₂ : DiffeologicalSpace X) :
    (d₁ ⊓ d₂).toPlots = d₁.toPlots ∩ d₂.toPlots := rfl

theorem toPlots_iInf {ι : Type*} {D : ι → DiffeologicalSpace X} :
    (⨅ i, D i).toPlots = ⋂ i, (D i).toPlots :=
  (gc_generateFrom X).u_iInf

theorem toPlots_sInf {D : Set (DiffeologicalSpace X)} : (sInf D).toPlots = ⋂ d ∈ D, d.toPlots :=
  (gc_generateFrom X).u_sInf

theorem generateFrom_union_toPlots (d₁ d₂ : DiffeologicalSpace X) :
    generateFrom (d₁.toPlots ∪ d₂.toPlots) = d₁ ⊔ d₂ :=
  (giGenerateFrom X).l_sup_u _ _

theorem generateFrom_iUnion_toPlots {ι : Type*} (D : ι → DiffeologicalSpace X) :
    generateFrom (⋃ i, (D i).toPlots) = ⨆ i, D i :=
  (giGenerateFrom X).l_iSup_u _

theorem generateFrom_inter_toPlots (d₁ d₂ : DiffeologicalSpace X) :
    generateFrom (d₁.toPlots ∩ d₂.toPlots) = d₁ ⊓ d₂ :=
  (giGenerateFrom X).l_inf_u _ _

theorem generateFrom_iInter_toPlots {ι : Type*} (D : ι → DiffeologicalSpace X) :
    generateFrom (⋂ i, (D i).toPlots) = ⨅ i, D i :=
  (giGenerateFrom X).l_iInf_u _

theorem generateFrom_iInter_of_generateFrom_eq_self {ι : Type*}
    (G : ι → Set ((n : ℕ) × (Eucl n → X)))
    (hG : ∀ i, (generateFrom (G i)).toPlots = G i) :
    generateFrom (⋂ i, G i) = ⨅ i, generateFrom (G i) :=
  (giGenerateFrom X).l_iInf_of_ul_eq_self G hG

theorem isPlot_inf_iff {d₁ d₂ : DiffeologicalSpace X} {n : ℕ} {p : Eucl n → X} :
    IsPlot[d₁ ⊓ d₂] p ↔ IsPlot[d₁] p ∧ IsPlot[d₂] p :=
  Set.ext_iff.1 (toPlots_inf d₁ d₂) ⟨n,p⟩

theorem isPlot_iInf_iff {ι : Type*} {D : ι → DiffeologicalSpace X} {n : ℕ} {p : Eucl n → X} :
    IsPlot[⨅ i, D i] p ↔ ∀ i, IsPlot[D i] p :=
  (Set.ext_iff.1 (toPlots_iInf (D := D)) ⟨n,p⟩).trans Set.mem_iInter

theorem isPlot_sInf_iff {D : Set (DiffeologicalSpace X)} {n : ℕ} {p : Eucl n → X} :
    IsPlot[sInf D] p ↔ ∀ d ∈ D, IsPlot[d] p :=
  (Set.ext_iff.1 (toPlots_sInf (D := D)) ⟨n,p⟩).trans Set.mem_iInter₂

/-- A map is a plot in the diffeology generated `g` iff it is constant or locally a
reparametrisation of maps in `g`. -/
lemma isPlot_generateFrom_iff (g : Set ((n : ℕ) × (Eucl n → X))) {n : ℕ} {p : Eucl n → X} :
    IsPlot[generateFrom g] p ↔ (∃ y, p = fun _ ↦ y) ∨ ∀ x, ∃ p' ∈ g,
      ∃ f, (∃ u ∈ 𝓝 x, ContDiffOn ℝ ∞ f u) ∧ p =ᶠ[𝓝 x] p'.2 ∘ f := by
  refine ⟨fun hp ↦ ?_, Or.rec (fun ⟨y, hy⟩ ↦ hy ▸ @isPlot_const _ (_) _ _) fun h ↦ ?_⟩
  · let d : DiffeologicalSpace X := mkOfPlotsOn {
      isPlotOn {n u} hu p := ∀ x ∈ u, p =ᶠ[𝓝 x] (fun _ ↦ p x) ∨
        ∃ p' ∈ g, ∃ f, (∃ v ∈ 𝓝 x, ContDiffOn ℝ ∞ f v) ∧ p =ᶠ[𝓝 x] p'.2 ∘ f
      isPlotOn_congr {n u} hu p q h := by
        refine forall₂_congr fun x hxu ↦ or_congr ?_ ?_
        · rw [h hxu]
          exact (h.eventuallyEq_of_mem (hu.mem_nhds hxu)).congr_left
        · refine exists_congr fun p' ↦ and_congr_right fun hp' ↦
            exists_congr fun f ↦ and_congr_right fun hf ↦ ?_
          exact (h.eventuallyEq_of_mem (hu.mem_nhds hxu)).congr_left
      isPlot {n p} := (∃ y, p = fun _ ↦ y) ∨ ∀ x, ∃ p' ∈ g,
        ∃ f, (∃ u ∈ 𝓝 x, ContDiffOn ℝ ∞ f u) ∧ p =ᶠ[𝓝 x] p'.2 ∘ f
      isPlotOn_univ {n p} := by
        refine ⟨fun h ↦ ?_, fun hp x _ ↦ hp.imp (fun ⟨_, hp⟩ ↦ by rw [hp]) (fun hp ↦ hp x)⟩
        have h' : IsClopen (p ⁻¹' (⋃ p' ∈ g, Set.range p'.2)) := by
          refine ⟨⟨isOpen_iff_mem_nhds.2 fun x hx ↦ ?_⟩, isOpen_iff_mem_nhds.2 fun x hx ↦ ?_⟩
          all_goals specialize h x trivial; rw [← Filter.eventually_mem_set]
          all_goals simp only [Set.mem_compl_iff, Set.mem_preimage] at hx ⊢
          · replace h := h.resolve_right fun ⟨p', hp', f, hf, hp⟩ ↦ hx <|
              Set.mem_iUnion₂_of_mem hp' <| hp.eq_of_nhds ▸ Set.mem_range_self _
            exact h.mono fun x' hx' ↦ hx' ▸ hx
          · refine h.rec (fun h ↦ ?_) (fun ⟨p', hp', f, hf, h⟩ ↦ ?_)
            · exact h.mono fun x' hx' ↦ hx' ▸ hx
            · exact h.mono fun x' hx' ↦ hx' ▸ Set.mem_iUnion₂_of_mem hp' (Set.mem_range_self _)
        refine (isClopen_iff.1 h').rec (fun h' ↦ .inl ?_) (fun h' ↦ .inr fun x ↦ ?_)
        · have := Nonempty.map p inferInstance
          refine IsLocallyConstant.exists_eq_const <| (IsLocallyConstant.iff_eventually_eq _).2
            fun x ↦ (h x trivial).rec id (fun ⟨p', hp', f, hf, h⟩ ↦ ?_)
          refine (Set.eq_empty_iff_forall_notMem.1 h' x ?_).elim
          exact Set.mem_iUnion₂_of_mem hp' <| h.eq_of_nhds ▸ Set.mem_range_self _
        · refine (h x trivial).rec (fun h ↦ ?_) id
          let ⟨p', hp', x', hx'⟩ := Set.mem_iUnion₂.1 <| (Set.eq_univ_iff_forall.1 h') x
          exact ⟨p', hp', fun _ ↦ x', ⟨_, Filter.univ_mem, contDiffOn_const⟩, (hx' ▸ h:)⟩
      isPlot_const {n x} :=  Or.inl ⟨x, rfl⟩
      isPlotOn_reparam {n m u v hu} hv {p f} h hp hf x hxv := by
        refine (hp _ (h hxv)).imp (fun hp ↦ ?_) (fun hp ↦ ?_)
        · exact hp.comp_tendsto <| hf.continuousOn.continuousAt (hv.mem_nhds hxv)
        · let ⟨p', hp', g, ⟨w, hw, hg⟩, hp⟩ := hp
          refine ⟨p', hp', g ∘ f, ⟨_, Filter.inter_mem (hv.mem_nhds hxv) <|
            hf.continuousOn.continuousAt (hv.mem_nhds hxv) hw, hg.comp_inter hf⟩, ?_⟩
          exact hp.comp_tendsto <| hf.continuousOn.continuousAt (hv.mem_nhds hxv)
      locality {n u} hu {p} hp x hxu := by
        obtain ⟨v, hv, hxv, hp⟩ := hp x hxu
        exact hp x hxv
    }
    refine DiffeologicalSpace.le_iff'.1 ?_ n p hp
    exact generateFrom_le_iff.2 fun n p hp ↦ .inr fun x ↦
      ⟨_, hp, id, ⟨_, Filter.univ_mem, contDiffOn_id⟩, .rfl⟩
  · refine (generateFrom g).locality <| forall_imp (fun x ⟨p', hp', f, ⟨u, hu, hf⟩, h⟩ ↦ ?_) h
    let ⟨v, hv, hv', hxv⟩ := mem_nhds_iff.1 <| Filter.inter_mem hu h
    refine ⟨v, hv', hxv, fun {m f'} hf' hf'' ↦ ?_⟩
    rw [show p ∘ f' = p'.2 ∘ f ∘ f' by ext x; exact (hv <| hf' x).2]
    exact @isPlot_reparam _ (_) _ _ _ _ (isPlot_generateFrom_of_mem hp')
      (hf.comp_contDiff hf'' (fun x ↦ (hv <| hf' x).1))

end DiffeologicalSpace

end CompleteLattice
