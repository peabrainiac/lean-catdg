import Orbifolds.Diffeology.Algebra.Group

/-!
# Smooth modules
This file introduces diffeological modules and the "fine diffeology",
the finest diffeology turning a given module into a diffeological module.
This is comparable to `Topology.Algebra.Module.ModuleTopology`, although the file
structure and naming are different because Mathlib (at the time of writing) does not have a
`TopologicalModule` class comparable to the `DiffeologicalVectorSpace` class introduced here.

While in practice we mostly care about diffeological vector spaces over `ℝ`, we work over
general rings here just in case.
-/

/-- A diffeological ring is a ring in which addition, negation and multiplication are smooth. -/
class DiffeologicalRing (R : Type*) [DiffeologicalSpace R] [Ring R] extends
    DiffeologicalAddGroup R, DSmoothMul R : Prop

/-- The main example we care about: `ℝ` is a diffeological ring. -/
instance : DiffeologicalRing ℝ where
  dsmooth_add := contDiff_add.dsmooth
  dsmooth_neg := contDiff_neg.dsmooth
  dsmooth_mul := contDiff_mul.dsmooth

/-- A diffeological module over a diffeological ring is a module for which addition, negation
  and scalar multiplication are smooth. -/
class DiffeologicalModule (R : Type*) [DiffeologicalSpace R] [Ring R] [DiffeologicalRing R]
    (X : Type*) [DiffeologicalSpace X] [AddCommGroup X] [Module R X] extends
    DiffeologicalAddGroup X, DSmoothSMul R X : Prop

/-- Normed spaces with their natural diffeologies are diffeological vector spaces. -/
instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X]
    [ContDiffCompatible X] : DiffeologicalModule ℝ X where
  dsmooth_add := contDiff_add.dsmooth
  dsmooth_neg := contDiff_neg.dsmooth
  dsmooth_smul := contDiff_smul.dsmooth

example {n : ℕ} : DiffeologicalModule ℝ (Eucl n) := inferInstance

theorem diffeologicalModule_sInf {R : Type*} [DiffeologicalSpace R] [Ring R]
    [DiffeologicalRing R] {X : Type*} [AddCommGroup X] [Module R X]
    {D : Set (DiffeologicalSpace X)} (h : ∀ d ∈ D, @DiffeologicalModule R _ _ _ X d _ _) :
    @DiffeologicalModule R _ _ _ X (sInf D) _ _ :=
  letI := sInf D
  { toDiffeologicalAddGroup := diffeologicalAddGroup_sInf fun d hd ↦
      (h d hd).toDiffeologicalAddGroup
    toDSmoothSMul := dsmoothSMul_sInf <| fun d hd ↦ (h d hd).toDSmoothSMul }

theorem diffeologicalModule_iInf {R : Type*} [DiffeologicalSpace R] [Ring R]
    [DiffeologicalRing R] {X : Type*} [AddCommGroup X] [Module R X] {ι : Type*}
    {D : ι → DiffeologicalSpace X} (h' : ∀ i, @DiffeologicalModule R _ _ _ X (D i) _ _) :
    @DiffeologicalModule R _ _ _ X (⨅ i, D i) _ _ := by
  rw [←sInf_range]; exact diffeologicalModule_sInf (Set.forall_mem_range.mpr h')

theorem diffeologicalModule_inf {R : Type*} [DiffeologicalSpace R] [Ring R]
    [DiffeologicalRing R] {X : Type*} [AddCommGroup X] [Module R X]
    {d₁ d₂ : DiffeologicalSpace X}
    (h₁ : @DiffeologicalModule R _ _ _ X d₁ _ _) (h₂ : @DiffeologicalModule R _ _ _ X d₂ _ _) :
    @DiffeologicalModule R _ _ _ X (d₁ ⊓ d₂) _ _ :=
  inf_eq_iInf d₁ d₂ ▸ diffeologicalModule_iInf fun b => (by cases b <;> assumption)

/-!
### Lattice of module diffeologies
Analogous to `GroupDiffeology G`, we define for any `R`-module `X` the type
`ModuleDiffeology R X` of all diffeologies that turn `X` into a diffeological module.
This is interesting because, like `DiffeologicalSpace X`, `ModuleDiffeology R X` is
always a complete lattice - its top element is always the indiscrete diffeology, while its
bottom element is generally nontrivial. Note that the discrete diffeology is not a module
diffeology because scalar multiplication fails to be continuous.
-/

/-- A module diffeology on a module `X` is a diffeology with which `X` is a
  diffeological module. -/
structure ModuleDiffeology (R : Type*) [DiffeologicalSpace R] [Ring R] [DiffeologicalRing R]
    (X : Type*) [AddCommGroup X] [Module R X] extends
    DiffeologicalSpace X, DiffeologicalModule R X

namespace ModuleDiffeology

variable {R : Type*} [DiffeologicalSpace R] [Ring R] [DiffeologicalRing R]
  {X : Type*} [AddCommGroup X] [Module R X]

def toAddGroupDiffeology (d : ModuleDiffeology R X) : AddGroupDiffeology X :=
  ⟨d.toDiffeologicalSpace, d.toDiffeologicalModule.toDiffeologicalAddGroup⟩

/-- A version of the global `dsmooth_add` suitable for dot notation. -/
theorem dsmooth_add' (d : ModuleDiffeology R X) :
    haveI := d.toDiffeologicalSpace
    DSmooth fun p : X × X => p.1 + p.2 :=
  d.toAddGroupDiffeology.dsmooth_add'

/-- A version of the global `dsmooth_neg` suitable for dot notation. -/
theorem dsmooth_neg' (d : ModuleDiffeology R X) :
    haveI := d.toDiffeologicalSpace
    DSmooth (Neg.neg : X → X) :=
  d.toAddGroupDiffeology.dsmooth_neg'

/-- A version of the global `dsmooth_smul` suitable for dot notation. -/
theorem dsmooth_smul' (d : ModuleDiffeology R X) :
    haveI := d.toDiffeologicalSpace
    DSmooth fun p : R × X => p.1 • p.2 := by
  letI := d.toDiffeologicalSpace
  haveI := d.toDiffeologicalModule
  exact dsmooth_smul

theorem toDiffeologicalSpace_injective :
    Function.Injective (toDiffeologicalSpace : ModuleDiffeology R X → DiffeologicalSpace X) :=
  fun f g h => by cases f; cases g; congr

theorem toAddGroupDiffeology_injective :
    Function.Injective (toAddGroupDiffeology : ModuleDiffeology R X → AddGroupDiffeology X) :=
  toDiffeologicalSpace_injective.of_comp (f := AddGroupDiffeology.toDiffeologicalSpace)

@[ext]
theorem ext' {d₁ d₂ : ModuleDiffeology R X} (h : d₁.1 = d₂.1) : d₁ = d₂ :=
  toDiffeologicalSpace_injective h

instance : PartialOrder (ModuleDiffeology R X) :=
  PartialOrder.lift toDiffeologicalSpace toDiffeologicalSpace_injective

theorem toDiffeologicalSpace_le {d₁ d₂ : ModuleDiffeology R X} :
    d₁.1 ≤ d₂.1 ↔ d₁ ≤ d₂ :=
  Iff.rfl

/-- The coarsest module diffeology that is finer than a given diffeology.
  Called `reflector` for the lack of a better name and because it is left-adjoint to
  `ModuleDiffeology.toDiffeologicalSpace`. -/
def reflector (d : DiffeologicalSpace X) : ModuleDiffeology R X :=
  ⟨sInf {d' | d ≤ d' ∧ @DiffeologicalModule R _ _ _ X d' _ _},
    diffeologicalModule_sInf fun _ h ↦ h.2⟩

lemma gc_toDiffeologicalSpace :
    GaloisConnection reflector (toDiffeologicalSpace (R := R) (X := X)) :=
  fun _ _ ↦ ⟨fun h ↦ (le_sInf fun _ h ↦ h.1).trans (toDiffeologicalSpace_le.2 h),
    fun h ↦ toDiffeologicalSpace_le.1 <| sInf_le ⟨h, toDiffeologicalModule _⟩⟩

/-- The galois insertion between `ModuleDiffeology R X` and `DiffeologicalSpace X` whose
  lower part sends each diffeology to the finest coarser module diffeology, and whose
  upper part sends each module diffeology to itself. -/
def gci_toDiffeologicalSpace :
    GaloisInsertion reflector (toDiffeologicalSpace (R := R) (X := X)) where
  gc := gc_toDiffeologicalSpace
  le_l_u _ := toDiffeologicalSpace_le.1 <| le_sInf fun _ h ↦ h.1
  choice d hd := ⟨d, le_antisymm (le_sInf fun _ h ↦ h.1) hd ▸
    (reflector d).toDiffeologicalModule⟩
  choice_eq _ h := ext' <| le_antisymm (le_sInf fun _ h ↦ h.1) h

instance : CompleteLattice (ModuleDiffeology R X) :=
  (gci_toDiffeologicalSpace).liftCompleteLattice

end ModuleDiffeology
