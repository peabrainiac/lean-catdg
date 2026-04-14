import CatDG.Diffeology.DiffSp
import CatDG.Diffeology.Algebra.Module
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Singular simplicial sets
Like topological spaces, we can associate to each diffeological space a *singular simplicial set*,
consisting of all *smooth singular simplicies* (i.e. smooth maps from the standard simplices) in it.
This defines a functor from `DiffSp ⥤ SSet`, which is right-adjoint to a *geometric realisation*
functor `SSet ⥤ DiffSp`.

## TODO
* generalise universe levels
* compare with corresponding functors for topological spaces
-/

universe u

open CategoryTheory

@[fun_prop]
lemma FunOnFinite.dsmooth_map
    (M : Type*) [AddCommMonoid M] [DiffeologicalSpace M] [DSmoothAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X → Y) :
    DSmooth (FunOnFinite.map (M := M) f) := by
  classical
  have := Fintype.ofFinite X
  refine dsmooth_pi (fun y ↦ ?_)
  simp only [FunOnFinite.map_apply_apply]
  exact dsmooth_finset_sum _ (fun _ _ ↦ dsmooth_apply _)

@[fun_prop]
lemma FunOnFinite.dsmooth_linearMap
    (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [DiffeologicalSpace M] [DSmoothAdd M]
    {X Y : Type*} [Finite X] [Finite Y] (f : X → Y) :
    DSmooth (FunOnFinite.linearMap R M f) :=
  FunOnFinite.dsmooth_map _ _

@[fun_prop]
lemma stdSimplex.dsmooth_map {R X Y : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    [DiffeologicalSpace R] [DiffeologicalRing R] [Fintype X] [Fintype Y] (f : X → Y) :
    DSmooth (stdSimplex.map (S := R) f) :=
  ((FunOnFinite.dsmooth_linearMap _ _ f).comp dsmooth_subtype_val).subtype_mk _

/-- The standard cosimplicial object in `DiffSp.{0}`, sending each `n : SimplexCategory` to the
standard `n`-simplex with the subspace diffeology. -/
@[simps! obj map]
noncomputable def SimplexCategory.toDiffSp₀ : SimplexCategory ⥤ DiffSp.{0} where
  obj n := DiffSp.of (stdSimplex ℝ (Fin (n.len + 1)))
  map f := DiffSp.ofHom ⟨_, stdSimplex.dsmooth_map f⟩
  map_id n := by ext; simp
  map_comp f g := by ext1; simp [hom_comp, stdSimplex.map_comp_apply]

/-- The standard cosimplicial object in `DiffSp.{u}`, sending each `n : SimplexCategory` to the
standard `n`-simplex with the subspace diffeology lifted to the universe `u`. -/
@[simps! obj map]
noncomputable def SimplexCategory.toDiffSp : SimplexCategory ⥤ DiffSp.{u} :=
  toDiffSp₀ ⋙ DiffSp.uliftFunctor

/-- The singular simplicial set functor for diffeological spaces, sending each diffeological space
to the simplicial set of all smooth singular simplices in it. -/
noncomputable def DiffSp.toSSet : DiffSp.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda SimplexCategory.toDiffSp

/-- The geometric realisation functor from simplicial sets to diffeological spaces.
TODO: generalise universe levels in `DiffSp.hasColimitsOfSize` and this. -/
noncomputable def SSet.toDiffSp : SSet.{0} ⥤ DiffSp.{0} :=
  SSet.stdSimplex.{0}.leftKanExtension SimplexCategory.toDiffSp

set_option backward.isDefEq.respectTransparency false in
/-- Geometric realization is left adjoint to the singular simplicial set construction. -/
noncomputable def sSetDiffSpAdj : SSet.toDiffSp ⊣ DiffSp.toSSet.{0} :=
  Presheaf.uliftYonedaAdjunction
    (SSet.stdSimplex.{0}.leftKanExtension SimplexCategory.toDiffSp)
    (SSet.stdSimplex.{0}.leftKanExtensionUnit SimplexCategory.toDiffSp)

instance : SSet.toDiffSp.IsLeftAdjoint := sSetDiffSpAdj.isLeftAdjoint
instance : DiffSp.toSSet.{0}.IsRightAdjoint := sSetDiffSpAdj.isRightAdjoint
