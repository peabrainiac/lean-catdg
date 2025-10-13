import CatDG.Diffeology.Induced

/-!
# Reflexive diffeological spaces

This file deals with diffeological spaces `X` that are *reflexive* in the sense that they are
fixed points of the adjunction between diffeological spaces and differential space, i.e. whose
diffeology is induced by the differential space structure that it induces. Reflexive diffeological
spaces correspond exactly to Frölicher spaces - see https://arxiv.org/abs/1712.04576v2.

Note that while differential spaces are certainly related we have not formalised them here, and
instead went with a more explicit characterisation of reflexive diffeological spaces.
-/

/-- A diffeological space is called reflexive if the diffeology induced by the
differential structure induced by the diffeology is again the diffeology itself.
Since we don't have differential spaces yet, this is formulated as every function
`p : Eucl n → X` for which all compositions with functions `X → ℝ` are smooth
being a plot. -/
class ReflexiveDiffeologicalSpace (X : Type*) [DiffeologicalSpace X] : Prop where
  isPlot_if : ∀ {n : ℕ} (p : Eucl n → X),
    (∀ f : X → ℝ, DSmooth f → DSmooth (f ∘ p)) → IsPlot p

/-- Finite-dimensional normed spaces with their natural diffeologies are reflexive. -/
instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [DiffeologicalSpace X] [ContDiffCompatible X] : ReflexiveDiffeologicalSpace X where
  isPlot_if := fun {n} p hp ↦ by
    let Φ := (toEuclidean (E := X)).trans (EuclideanSpace.equiv _ ℝ)
    refine isPlot_iff_contDiff.2 <| Φ.comp_contDiff_iff.1 (contDiff_pi.2 fun i ↦ ?_)
    exact (hp _ (((ContinuousLinearMap.proj i).contDiff).comp Φ.contDiff).dsmooth).contDiff

/-- The diffeology induced by the differential space structure induced by the diffeology `d`. -/
def DiffeologicalSpace.toReflexive {X : Type*} {d : DiffeologicalSpace X} :
    DiffeologicalSpace X where
  plots n := { p | ∀ f : X → ℝ, DSmooth f → DSmooth (f ∘ p)}
  constant_plots := fun _ _ _ ↦ dsmooth_const
  plot_reparam := fun hp hf g hg ↦ (hp g hg).comp hf.dsmooth
  locality := fun {n p} h f hf ↦ IsPlot.dsmooth <| locality fun x ↦ by
    let ⟨u, hu, hxu, h⟩ := h x
    exact ⟨u, hu, hxu, fun hg hg' ↦ (h hg hg' f hf).isPlot⟩

/-- A function `X → Y` into a reflexive diffeological space is smooth with respect to
`dX : DiffeologicalSpace X` iff it is smooth with respect to `dX.toReflexive`. -/
lemma dsmooth_toReflexive_iff {X Y : Type*} {dX : DiffeologicalSpace X}
    [DiffeologicalSpace Y] [ReflexiveDiffeologicalSpace Y] {f : X → Y} :
    DSmooth[dX.toReflexive,_] f ↔ DSmooth[dX,_] f :=
  ⟨fun h _ _ hp ↦ h _ _ fun _ hg ↦ (hg _ _ hp).dsmooth,
    fun hf _ _ hp ↦ ReflexiveDiffeologicalSpace.isPlot_if _ fun _ hg ↦ hp _ (hg.comp hf)⟩

/-- `d.toReflexive` is a reflexive diffeology for any diffeology `d`. -/
lemma reflexiveDiffeologicalSpace_toReflexive {X : Type*} {d : DiffeologicalSpace X} :
    @ReflexiveDiffeologicalSpace X d.toReflexive :=
  @ReflexiveDiffeologicalSpace.mk X (_) fun _ h _ hf ↦ h _ <| dsmooth_toReflexive_iff.2 hf

/-- `d.toReflexive` is always at least as coarse as `d`. -/
lemma DiffeologicalSpace.le_toReflexive {X : Type*} {d : DiffeologicalSpace X} :
    d ≤ d.toReflexive :=
  le_iff'.2 fun _ _ hp _ hf ↦ (hf _ _ hp).dsmooth

lemma DiffeologicalSpace.eq_toReflexive_iff {X : Type*} {d : DiffeologicalSpace X} :
    d = d.toReflexive ↔ @ReflexiveDiffeologicalSpace X d :=
  ⟨fun h ↦ h ▸ reflexiveDiffeologicalSpace_toReflexive,
    fun h ↦ le_antisymm le_toReflexive <| le_iff'.2 fun _ _ hp ↦ h.isPlot_if _ hp⟩

namespace ReflexiveDiffeologicalSpace

/-- Type synonym equipped with the reflexive diffeology induced by the diffeology on `X`. -/
def of (X : Type*) := X

instance {X : Type*} [d : DiffeologicalSpace X] : DiffeologicalSpace (of X) :=
  d.toReflexive

instance {X : Type*} [DiffeologicalSpace X] : ReflexiveDiffeologicalSpace (of X) :=
  reflexiveDiffeologicalSpace_toReflexive

/-- The natural map from a diffeological space to its type synonym with the reflexive diffeology. -/
def unit {X : Type*} : X → (of X) := id

lemma dsmooth_unit {X : Type*} [DiffeologicalSpace X] : DSmooth (unit : X → _) :=
  fun _ _ hp _ hf ↦ (hf _ _ hp).dsmooth

end ReflexiveDiffeologicalSpace

/-- The lattice of all reflexive diffeologies on `X`. -/
structure ReflexiveDiffeology (X : Type*) extends
    DiffeologicalSpace X, ReflexiveDiffeologicalSpace X

theorem ReflexiveDiffeology.toDiffeologicalSpace_injective {X : Type*} :
    Function.Injective (toDiffeologicalSpace : ReflexiveDiffeology X → DiffeologicalSpace X) :=
  fun d d' h ↦ by cases d; cases d'; congr

@[ext]
theorem ReflexiveDiffeology.ext' {X : Type*} {d₁ d₂ : ReflexiveDiffeology X}
    (h : d₁.1 = d₂.1) : d₁ = d₂ :=
  toDiffeologicalSpace_injective h

instance {X : Type*} : PartialOrder (ReflexiveDiffeology X) :=
  PartialOrder.lift _ ReflexiveDiffeology.toDiffeologicalSpace_injective

@[simp]
theorem ReflexiveDiffeology.toDiffeologicalSpace_le {X : Type*} {d₁ d₂ : ReflexiveDiffeology X} :
    d₁.1 ≤ d₂.1 ↔ d₁ ≤ d₂ :=
  Iff.rfl

def DiffeologicalSpace.toReflexiveDiffeology {X : Type*} (d : DiffeologicalSpace X) :
    ReflexiveDiffeology X := ⟨d.toReflexive, reflexiveDiffeologicalSpace_toReflexive⟩

lemma DiffeologicalSpace.gc_toReflexiveDiffeology (X : Type*) :
    GaloisConnection toReflexiveDiffeology (@ReflexiveDiffeology.toDiffeologicalSpace X) :=
  fun _ d₂ ↦ ⟨fun h ↦ le_toReflexive.trans h,
    fun h ↦ le_iff'.2 fun _ _ hp ↦ d₂.2.isPlot_if _ fun _ hf ↦ hp _ (dsmooth_le_dom h hf)⟩

/-- The Galois insertion of reflexive diffeologies into all diffeologies on a type. -/
def DiffeologicalSpace.giToReflexiveDiffeology (X : Type*) :
    GaloisInsertion toReflexiveDiffeology (@ReflexiveDiffeology.toDiffeologicalSpace X) where
  gc := gc_toReflexiveDiffeology X
  le_l_u _ := le_iff'.2 fun _ _ hp _ hf ↦ (hf _ _ hp).dsmooth
  choice d h := ⟨d, ⟨fun p hp ↦ le_iff'.1 h _ p hp⟩⟩
  choice_eq _ h := le_antisymm le_toReflexive h

instance {X : Type*} : CompleteLattice (ReflexiveDiffeology X) :=
  (DiffeologicalSpace.giToReflexiveDiffeology X).liftCompleteLattice

/- Note: most direct corollaries of the Galois insertion don't have their own lemmas yet,
only those on suprema and infima do. -/

lemma DiffeologicalSpace.toReflexiveDiffeology_sup {X : Type*} (d₁ d₂ : DiffeologicalSpace X) :
    (d₁ ⊔ d₂).toReflexiveDiffeology = d₁.toReflexiveDiffeology ⊔ d₂.toReflexiveDiffeology :=
  (gc_toReflexiveDiffeology X).l_sup

lemma DiffeologicalSpace.toReflexiveDiffeology_iSup {X : Type*} {ι : Type*}
    {D : ι → DiffeologicalSpace X} :
    (⨆ i, D i).toReflexiveDiffeology = ⨆ i, (D i).toReflexiveDiffeology :=
  (gc_toReflexiveDiffeology X).l_iSup

lemma DiffeologicalSpace.toReflexiveDiffeology_sSup {X : Type*}
    {D : Set (DiffeologicalSpace X)} :
    (sSup D).toReflexiveDiffeology = ⨆ d ∈ D, d.toReflexiveDiffeology :=
  (gc_toReflexiveDiffeology X).l_sSup

lemma ReflexiveDiffeology.toDiffeologicalSpace_inf {X : Type*} (d₁ d₂ : ReflexiveDiffeology X) :
    (d₁ ⊓ d₂).toDiffeologicalSpace = d₁.toDiffeologicalSpace ⊓ d₂.toDiffeologicalSpace :=
  (DiffeologicalSpace.gc_toReflexiveDiffeology X).u_inf

lemma ReflexiveDiffeology.toDiffeologicalSpace_iInf {X : Type*} {ι : Type*}
    {D : ι → ReflexiveDiffeology X} :
    (⨅ i, D i).toDiffeologicalSpace = ⨅ i, (D i).toDiffeologicalSpace :=
  (DiffeologicalSpace.gc_toReflexiveDiffeology X).u_iInf

lemma ReflexiveDiffeology.toDiffeologicalSpace_sInf {X : Type*} {D : Set (ReflexiveDiffeology X)} :
    (sInf D).toDiffeologicalSpace = ⨅ d ∈ D, d.toDiffeologicalSpace :=
  (DiffeologicalSpace.gc_toReflexiveDiffeology X).u_sInf

/-- Infima (in the lattice of diffeologies) of reflexive diffeologies are again reflexive. -/
lemma ReflexiveDiffeologicalSpace.inf {X : Type*} {d₁ d₂ : DiffeologicalSpace X}
    (h₁ : @ReflexiveDiffeologicalSpace X d₁) (h₂ : @ReflexiveDiffeologicalSpace X d₂) :
    @ReflexiveDiffeologicalSpace X (d₁ ⊓ d₂) :=
  ReflexiveDiffeology.toReflexiveDiffeologicalSpace (⟨d₁, h₁⟩ ⊓ ⟨d₂, h₂⟩)

/-- Infima (in the lattice of diffeologies) of reflexive diffeologies are again reflexive. -/
lemma ReflexiveDiffeologicalSpace.iInf {X : Type*} {ι : Type*} {D : ι → DiffeologicalSpace X}
    (h : ∀ i, @ReflexiveDiffeologicalSpace X (D i)) :
    @ReflexiveDiffeologicalSpace X (⨅ i, D i) :=
  (ReflexiveDiffeology.toDiffeologicalSpace_iInf ▸
    ReflexiveDiffeology.toReflexiveDiffeologicalSpace (⨅ i, ⟨D i, h i⟩):)
