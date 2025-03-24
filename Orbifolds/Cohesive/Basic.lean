import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Cohesive categories
A topos `C` is called cohesive over another topos `D` (typically `Type`) if it is equipped with
a quadruple `π₀ ⊣ disc ⊣ Γ ⊣ codisc` of adjoint functors between them, the first of which
preserves finite products, and the second and fourth of which are fully faithful. We formalise this
here by defining a typeclass `CohesiveStructure C D` carrying such a quadruple between arbitrary
categories `C` and `D`, since mathlib does not much on topoi yet.

See https://ncatlab.org/nlab/show/cohesive+topos for cohesive topoi, and also the paper
"Axiomatic Cohesion" by Lawvere for more general cohesive categories.

-/

universe u v u' v'

open CategoryTheory Limits

namespace CategoryTheory

/-- Typeclass equipping a category with the adjoint quadruple of functors that is also used to
define e.g. cohesive topoi. Since topoi are not in mathlib yet I am stating this for general
categories, but it should probably be changed to something more specific like cohesive topoi or
"categories of cohesion" in the sense of Lawvere. -/
class CohesiveStructure (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] where
  π₀ : C ⥤ D
  disc : D ⥤ C
  Γ : C ⥤ D
  codisc : D ⥤ C
  π₀DiscAdj : π₀ ⊣ disc
  discΓAdj : disc ⊣ Γ
  ΓCodiscAdj : Γ ⊣ codisc
  preservesProducts_π₀ {ι : Type u'} [Fintype ι] : PreservesLimitsOfShape (Discrete ι) π₀
  fullyFaithfulDisc : disc.FullyFaithful
  fullyFaithfulCodisc : codisc.FullyFaithful

namespace Cohesive

export CategoryTheory.CohesiveStructure (π₀ disc Γ codisc π₀DiscAdj discΓAdj ΓCodiscAdj
  ΓCodiscAdj preservesProducts_π₀ fullyFaithfulDisc fullyFaithfulCodisc)

variable (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] [CohesiveStructure C D]

instance : (π₀ : C ⥤ D).IsLeftAdjoint := π₀DiscAdj.isLeftAdjoint

instance : (disc : D ⥤ C).IsRightAdjoint := π₀DiscAdj.isRightAdjoint

instance : (disc : D ⥤ C).IsLeftAdjoint := discΓAdj.isLeftAdjoint

instance : (Γ : C ⥤ D).IsRightAdjoint := discΓAdj.isRightAdjoint

instance : (Γ : C ⥤ D).IsLeftAdjoint := ΓCodiscAdj.isLeftAdjoint

instance : (codisc : D ⥤ C).IsRightAdjoint := ΓCodiscAdj.isRightAdjoint

instance {ι : Type u'} [Fintype ι] : PreservesLimitsOfShape (Discrete ι) (π₀ : C ⥤ D) :=
  preservesProducts_π₀

instance : (disc : D ⥤ C).Full := fullyFaithfulDisc.full

instance : (disc : D ⥤ C).Faithful := fullyFaithfulDisc.faithful

instance : (codisc : D ⥤ C).Full := fullyFaithfulCodisc.full

instance : (codisc : D ⥤ C).Faithful := fullyFaithfulCodisc.faithful

example : IsIso (π₀DiscAdj (C := C) (D := D)).counit := inferInstance

example : IsIso (discΓAdj (C := C) (D := D)).unit := inferInstance

example : IsIso (ΓCodiscAdj (C := C) (D := D)).counit := inferInstance

/-- The shape modality on a cohesive category. -/
@[simps!]
def shape : Monad C :=
  (π₀DiscAdj (D := D)).toMonad

/-- The flat modality on a cohesive category. -/
@[simps!]
def flat : Comonad C :=
  (discΓAdj (D := D)).toComonad

/-- The sharp modality on a cohesive category. -/
@[simps!]
def sharp : Monad C :=
  (ΓCodiscAdj (D := D)).toMonad

/-- The shape modality is adjoint to the flat modality. -/
@[simps!]
def shapeFlatAdj : (shape C D).toFunctor ⊣ (flat C D).toFunctor :=
  π₀DiscAdj.comp discΓAdj

/-- The flat modality is adjoint to the sharp modality. -/
@[simps!]
def flatSharpAdj : (flat C D).toFunctor ⊣ (sharp C D).toFunctor :=
  ΓCodiscAdj.comp discΓAdj

instance : (shape C D).IsLeftAdjoint := (shapeFlatAdj C D).isLeftAdjoint

instance : (flat C D).IsRightAdjoint := (shapeFlatAdj C D).isRightAdjoint

instance : (flat C D).IsLeftAdjoint := (flatSharpAdj C D).isLeftAdjoint

instance : (sharp C D).IsRightAdjoint := (flatSharpAdj C D).isRightAdjoint

/-- See https://ncatlab.org/nlab/show/cohesive+topos#CoincidenceOfTransformsForAdjointTriple.
TODO: generalise & move to Mathlib.CategoryTheory.Adjunction.Triple
-/
lemma counit_unit_diskΓAdj_eq_counit_unit_π₀DiscAdj : (Functor.associator _ _ _).inv ≫
    whiskerRight (discΓAdj (C := C) (D := D)).counit π₀ ≫ π₀.leftUnitor.hom ≫
    π₀.rightUnitor.inv ≫ whiskerLeft π₀ (discΓAdj (C := C) (D := D)).unit =
    whiskerLeft Γ π₀DiscAdj.counit ≫ Γ.rightUnitor.hom ≫ Γ.leftUnitor.inv ≫
    whiskerRight π₀DiscAdj.unit Γ ≫ (Functor.associator _ _ _).hom := by
  ext X
  dsimp; simp only [Category.id_comp, Category.comp_id]
  refine .trans ?_ <| π₀DiscAdj.counit_naturality <| (whiskerRight π₀DiscAdj.unit Γ).app X
  rw [whiskerRight_app, (asIso (discΓAdj.counit.app (disc.obj _))).eq_comp_inv.2
    (discΓAdj.counit_naturality (π₀DiscAdj.unit.app X))]
  rw [← (asIso _).comp_hom_eq_id.1 <| discΓAdj.left_triangle_components (π₀.obj X)]
  simp

/-- The points-to-pieces transform `Γ ⟶ π₀`. The other natural transformation that is also
often called the points to pieces transform is the image of this under `disc`. -/
@[simps!]
noncomputable def pointsToPieces : (Γ : C ⥤ D) ⟶ π₀ :=
  Γ.leftUnitor.inv ≫ whiskerRight π₀DiscAdj.unit Γ ≫ (Functor.associator _ _ _).hom ≫
    inv (whiskerLeft π₀ discΓAdj.unit) ≫ π₀.rightUnitor.hom

/-- An alternate form of `pointsToPieces` in terms of counits instead of units. -/
lemma pointsToPieces_eq : pointsToPieces C D = Γ.rightUnitor.inv ≫
    inv (whiskerLeft Γ π₀DiscAdj.counit) ≫ (Functor.associator _ _ _).inv ≫
    whiskerRight discΓAdj.counit π₀ ≫ π₀.leftUnitor.hom := by
  ext X; dsimp [pointsToPieces]
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Category.comp_id, Category.id_comp]
  rw [IsIso.comp_inv_eq]
  simpa using (congr_app (counit_unit_diskΓAdj_eq_counit_unit_π₀DiscAdj C D) X).symm

/-- The points-to-pieces transform `flat C D ⟶ shape C D` in `C` - since `flat C D` and
`shape C D` are the compositions of `Γ` and `π₀` with `disc`, we add the prefix "disc" to
distinguish it from the points-to-pieces transform `pointsToPieces C D : Γ ⟶ π₀` in `D`. -/
@[simps!]
def discPointsToPieces : (flat C D).toFunctor ⟶ (shape C D).toFunctor :=
  (flat C D).ε ≫ (shape C D).η

/-- The components of `discPointsToPieces C D` are `discΓAdj`-adjunct to the image of the unit
components of `shape C D` under `Γ`. -/
lemma discΓΑdj_homEquiv_discPointsToPieces {X : C} :
    (discΓAdj.homEquiv _ _) ((discPointsToPieces C D).app X) = Γ.map (π₀DiscAdj.unit.app X) := by
  rw [discPointsToPieces_app, Adjunction.homEquiv_apply]; simp

/-- The points-to-pieces transform `flat C D ⟶ shape C D` in `C` is the image of the
points-to-pieces transform `Γ ⟶ π₀` in `D` under `disc : D ⥤ C`. -/
lemma discPointsToPieces_app_eq_disc_pointsToPieces {X : C} :
    (discPointsToPieces C D).app X = disc.map ((pointsToPieces C D).app X) := by
  refine ((discΓAdj.homEquiv _ _).symm_apply_apply _).symm.trans ?_
  rw [discΓΑdj_homEquiv_discPointsToPieces]; dsimp
  rw [Adjunction.homEquiv_symm_apply, ← Adjunction.inv_map_unit, ← disc.map_inv,
    ← disc.map_comp, pointsToPieces_app]

/-- The points-to-pieces transform `flat C D ⟶ shape C D` in `C` is the image of the
points-to-pieces transform `Γ ⟶ π₀` in `D` under `disc : D ⥤ C`. -/
lemma discPointsToPieces_eq_pointsToPieces_disc :
    discPointsToPieces C D = whiskerRight (pointsToPieces C D) disc := by
  ext X; exact discPointsToPieces_app_eq_disc_pointsToPieces C D

/-- Cohesion of `C` over `D` is said to satisfy *pieces have points* if the components of the
points-to-pieces transformation in `D` are epimorphisms. -/
abbrev PiecesHavePoints := ∀ X, Epi ((pointsToPieces C D).app X)

instance [PiecesHavePoints C D] : Epi (pointsToPieces C D) := NatTrans.epi_of_epi_app _

/-- Cohesion of `C` over `D` satisfies *pieces have points* iff the components of the
points-to-pieces transformation in `C` are epimorphisms. -/
lemma piecesHavePoints_iff_epi_discPointsToPieces_app :
    PiecesHavePoints C D ↔ ∀ X, Epi ((discPointsToPieces C D).app X) := by
  refine ⟨forall_imp fun X h ↦ ?_, forall_imp fun X h ↦ ?_⟩
  · rw [discPointsToPieces_app_eq_disc_pointsToPieces]; exact disc.map_epi _
  · --suffices Epi (discΓAdj.unit.app (π₀.obj X)) by sorry
    rw [pointsToPieces_app]
    -- TODO replace with `refine epi_comp' ?_ inferInstance` next time mathlib is bumped
    refine @epi_comp _ _ _ _ _ _ ?_ _ _
    rw [← discΓΑdj_homEquiv_discPointsToPieces C D, Adjunction.homEquiv_apply]
    infer_instance

instance [PiecesHavePoints C D] : Epi (discPointsToPieces C D) := by
  have := (piecesHavePoints_iff_epi_discPointsToPieces_app C D).1 ‹_›
  exact NatTrans.epi_of_epi_app _

end Cohesive

end CategoryTheory
