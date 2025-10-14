import CatDG.ForMathlib.Triple
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Quadruple
import Mathlib.CategoryTheory.Limits.Preserves.Finite

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

open CategoryTheory Limits Functor Adjunction

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
  preservesFiniteProducts_π₀ : PreservesFiniteProducts π₀
  fullyFaithfulDisc : disc.FullyFaithful
  fullyFaithfulCodisc : codisc.FullyFaithful

namespace Cohesive

export CategoryTheory.CohesiveStructure (π₀ disc Γ codisc π₀DiscAdj discΓAdj ΓCodiscAdj
  ΓCodiscAdj preservesFiniteProducts_π₀ fullyFaithfulDisc fullyFaithfulCodisc)

variable (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] [CohesiveStructure C D]

instance : (π₀ : C ⥤ D).IsLeftAdjoint := π₀DiscAdj.isLeftAdjoint

instance : (disc : D ⥤ C).IsRightAdjoint := π₀DiscAdj.isRightAdjoint

instance : (disc : D ⥤ C).IsLeftAdjoint := discΓAdj.isLeftAdjoint

instance : (Γ : C ⥤ D).IsRightAdjoint := discΓAdj.isRightAdjoint

instance : (Γ : C ⥤ D).IsLeftAdjoint := ΓCodiscAdj.isLeftAdjoint

instance : (codisc : D ⥤ C).IsRightAdjoint := ΓCodiscAdj.isRightAdjoint

instance : PreservesFiniteProducts (π₀ : C ⥤ D) :=
  preservesFiniteProducts_π₀

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

def π₀DiscΓCodiscQuadruple : Quadruple (π₀ : C ⥤ D) disc Γ codisc where
  adj₁ := π₀DiscAdj
  adj₂ := discΓAdj
  adj₃ := ΓCodiscAdj

abbrev π₀DiscΓTriple : Triple (π₀ : C ⥤ D) disc Γ := (π₀DiscΓCodiscQuadruple C D).leftTriple

abbrev discΓCodiscTriple : Triple (disc : D ⥤ C) Γ codisc :=
  (π₀DiscΓCodiscQuadruple C D).rightTriple

section PointsToPieces

/-- The points-to-pieces transform `Γ ⟶ π₀`. The other natural transformation that is also
often called the points to pieces transform is the image of this under `disc`. -/
@[simps!]
noncomputable def pointsToPieces : (Γ : C ⥤ D) ⟶ π₀ :=
  (π₀DiscΓTriple C D).rightToLeft

/-- Formula for `pointsToPieces C D` in terms of the whiskered units of the adjunctions. -/
lemma pointsToPieces_eq_units : pointsToPieces C D = Γ.leftUnitor.inv ≫
    whiskerRight π₀DiscAdj.unit Γ ≫
    (associator _ _ _).hom ≫ inv (whiskerLeft π₀ discΓAdj.unit) ≫ π₀.rightUnitor.hom :=
  (π₀DiscΓTriple C D).rightToLeft_eq_units

/-- Formula for `pointsToPieces C D` in terms of the whiskered counits of the adjunctions. -/
lemma pointsToPieces_eq_counits : pointsToPieces C D = Γ.rightUnitor.inv ≫
    inv (whiskerLeft Γ π₀DiscAdj.counit) ≫ (associator _ _ _).inv ≫
    whiskerRight discΓAdj.counit π₀ ≫ π₀.leftUnitor.hom :=
  (π₀DiscΓTriple C D).rightToLeft_eq_counits

/-- The points-to-pieces transform `flat C D ⟶ shape C D` in `C` - since `flat C D` and
`shape C D` are the compositions of `Γ` and `π₀` with `disc`, we add the prefix "disc" to
distinguish it from the points-to-pieces transform `pointsToPieces C D : Γ ⟶ π₀` in `D`. -/
@[simps!]
def discPointsToPieces : (flat C D).toFunctor ⟶ (shape C D).toFunctor :=
  (flat C D).ε ≫ (shape C D).η

/-- The components of `discPointsToPieces C D` are `discΓAdj`-adjunct to the image of the unit
components of `shape C D` under `Γ`. -/
lemma discΓΑdj_homEquiv_discPointsToPieces {X : C} :
    (discΓAdj.homEquiv _ _) ((discPointsToPieces C D).app X) = Γ.map (π₀DiscAdj.unit.app X) :=
  (π₀DiscΓTriple C D).homEquiv_counit_unit_app_eq_H_map_unit

/-- The components of `discPointsToPieces C D` are `π₀DiscAdj`-adjunct to the image of the
counit components of `flat C D` under `π₀`. -/
lemma π₀DiscAdj_homEquiv_symm_discPointsToPieces {X : C} :
    (π₀DiscAdj.homEquiv _ _).symm ((discPointsToPieces C D).app X) =
    π₀.map (discΓAdj.counit.app X) :=
  (π₀DiscΓTriple C D).homEquiv_symm_counit_unit_app_eq_F_map_counit

/-- The points-to-pieces transform `flat C D ⟶ shape C D` in `C` is the image of the
points-to-pieces transform `Γ ⟶ π₀` in `D` under `disc : D ⥤ C`. -/
lemma discPointsToPieces_app_eq_disc_pointsToPieces {X : C} :
    (discPointsToPieces C D).app X = disc.map ((pointsToPieces C D).app X) :=
  (π₀DiscΓTriple C D).counit_unit_app_eq_map_HToF

/-- The points-to-pieces transform `flat C D ⟶ shape C D` in `C` is the image of the
points-to-pieces transform `Γ ⟶ π₀` in `D` under `disc : D ⥤ C`. -/
lemma discPointsToPieces_eq_pointsToPieces_disc :
    discPointsToPieces C D = whiskerRight (pointsToPieces C D) disc := by
  ext X; exact discPointsToPieces_app_eq_disc_pointsToPieces C D

end PointsToPieces

section DiscToCodisc

/-- The canonical natural transformation `disc ⟶ codisc`. -/
@[simps!]
noncomputable def discToCodisc : (disc : D ⥤ C) ⟶ codisc :=
  (discΓCodiscTriple C D).leftToRight

/-- Formula for `discToCodisc C D` in terms of the whiskered units of the adjunctions. -/
noncomputable def discToCodisc_eq_units : discToCodisc C D = disc.rightUnitor.inv ≫
    whiskerLeft disc ΓCodiscAdj.unit ≫ (associator _ _ _).inv ≫
    inv (whiskerRight discΓAdj.unit codisc) ≫ codisc.leftUnitor.hom :=
  rfl

/-- Formula for `discToCodisc C D` in terms of the whiskered counits of the adjunctions. -/
noncomputable def discToCodisc_eq_counits : discToCodisc C D = disc.leftUnitor.inv ≫
    inv (whiskerRight ΓCodiscAdj.counit disc) ≫ (associator _ _ _).hom ≫
    whiskerLeft codisc discΓAdj.counit ≫ codisc.rightUnitor.hom :=
  (discΓCodiscTriple C D).leftToRight_eq_counits

/-- The canonical natural transformation `flat C D ⟶ sharp C D`. -/
@[simps!]
def flatToSharp : (flat C D).toFunctor ⟶ (sharp C D).toFunctor :=
  (flat C D).ε ≫ (sharp C D).η

/-- The components of `flatToSharp C D` are `discΓAdj`-adjunct to the image of the unit
components of `sharp C D` under `Γ`. -/
lemma discΓΑdj_homEquiv_flatToSharp {X : C} :
    (discΓAdj.homEquiv _ _) ((flatToSharp C D).app X) = Γ.map (ΓCodiscAdj.unit.app X) :=
  (discΓCodiscTriple C D).homEquiv_counit_unit_app_eq_G_map_unit

/-- The components of `flatToSharp C D` are `ΓCodiscAdj`-adjunct to the image of the
counit components of `flat C D` under `Γ`. -/
lemma ΓCodiscAdj_homEquiv_symm_flatToSharp {X : C} :
    (ΓCodiscAdj.homEquiv _ _).symm ((flatToSharp C D).app X) = Γ.map (discΓAdj.counit.app X) :=
  (discΓCodiscTriple C D).homEquiv_symm_counit_unit_app_eq_G_map_counit

/-- The components of the natural transformation `flat C D ⟶ shape C D` are simply the
components of the discrete-to-codiscrete transform `disc ⟶ codisc` at `Γ`. -/
lemma flatToSharp_app_eq_discToCodisc_Γ {X : C} :
    (flatToSharp C D).app X = (discToCodisc C D).app (Γ.obj X) :=
  (discΓCodiscTriple C D).counit_unit_app_eq_FToH_app

/-- The points-to-pieces transform `flat C D ⟶ shape C D` in `C` is the image of the
points-to-pieces transform `Γ ⟶ π₀` in `D` under `disc : D ⥤ C`. -/
lemma flatToSharp_eq_Γ_discToCodisc :
    flatToSharp C D = whiskerLeft Γ (discToCodisc C D) :=
  (discΓCodiscTriple C D).whiskerLeft_leftToRight.symm

end DiscToCodisc

section PiecesHavePoints

/-- Cohesion of `C` over `D` is said to satisfy *pieces have points* if the components of the
points-to-pieces transformation in `D` are epimorphisms. -/
abbrev PiecesHavePoints := ∀ X, Epi ((pointsToPieces C D).app X)

instance [PiecesHavePoints C D] : Epi (pointsToPieces C D) := NatTrans.epi_of_epi_app _

/-- Cohesion of `C` over `D` satisfies *pieces have points* iff the components of the
points-to-pieces transformation in `C` are epimorphisms. -/
lemma piecesHavePoints_iff_epi_discPointsToPieces_app :
    PiecesHavePoints C D ↔ ∀ X, Epi ((discPointsToPieces C D).app X) :=
  forall_congr' fun _ ↦ (π₀DiscΓTriple C D).epi_rightToLeft_app_iff

instance [PiecesHavePoints C D] {X : C} : Epi ((discPointsToPieces C D).app X) := by
  exact (piecesHavePoints_iff_epi_discPointsToPieces_app C D).1 ‹_› X

instance [PiecesHavePoints C D] : Epi (discPointsToPieces C D) :=
  NatTrans.epi_of_epi_app _

/-- Cohesion of `C` over `D` satisfies *pieces have points* iff the unit components of
`shape C D` are mapped to epimorphisms by `Γ`. -/
lemma piecesHavePoints_iff_epi_Γ_shape_unit :
    PiecesHavePoints C D ↔ ∀ X : C, Epi ((Γ : C ⥤ D).map ((shape C D).η.app X)) := by
  refine forall_congr' fun X ↦ ?_
  exact (π₀DiscΓTriple C D).epi_rightToLeft_app_iff_epi_map_adj₁_unit_app

instance [PiecesHavePoints C D] {X : C} : Epi ((Γ : C ⥤ D).map ((shape C D).η.app X)) := by
  exact (piecesHavePoints_iff_epi_Γ_shape_unit C D).1 ‹_› X

instance [PiecesHavePoints C D] : Epi (whiskerRight (shape C D).η (Γ : C ⥤ D)) :=
  @NatTrans.epi_of_epi_app _ _ _ _ _ _ _ <| (piecesHavePoints_iff_epi_Γ_shape_unit C D).1 ‹_›

/-- Cohesion of `C` over `D` satisfies *pieces have points* iff the components of the
discrete-to-codiscrete transformation are monomorphisms. -/
lemma piecesHavePoints_iff_mono_discToCodisc_app :
    PiecesHavePoints C D ↔ ∀ X : D, Mono ((discToCodisc C D).app X) :=
  (π₀DiscΓCodiscQuadruple C D).epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app

instance [PiecesHavePoints C D] {X : D} : Mono ((discToCodisc C D).app X) := by
  exact (piecesHavePoints_iff_mono_discToCodisc_app C D).1 ‹_› X

instance [PiecesHavePoints C D] : Mono (discToCodisc C D) :=
  NatTrans.mono_of_mono_app _

/-- Cohesion of `C` over `D` satisfies *pieces have points* iff the components of the
flat-to-sharp transformation are monomorphisms. -/
lemma piecesHavePoints_iff_mono_flatToSharp_app :
    PiecesHavePoints C D ↔ ∀ X : C, Mono ((flatToSharp C D).app X) := by
  exact (piecesHavePoints_iff_mono_discToCodisc_app C D).trans <|
    (discΓCodiscTriple C D).mono_leftToRight_app_iff

instance [PiecesHavePoints C D] {X : C} : Mono ((flatToSharp C D).app X) := by
  exact (piecesHavePoints_iff_mono_flatToSharp_app C D).1 ‹_› X

instance [PiecesHavePoints C D] : Mono (flatToSharp C D) :=
  NatTrans.mono_of_mono_app _

/-- Cohesion of `C` over `D` satisfies *pieces have points* iff the unit components of
`sharp C D` on discrete objects are monomorphisms. -/
lemma piecesHavePoints_iff_mono_sharp_unit_disc :
    PiecesHavePoints C D ↔ ∀ X : D, Mono ((sharp C D).η.app (disc.obj X)) := by
  rw [piecesHavePoints_iff_mono_discToCodisc_app]
  exact forall_congr' fun _ ↦ (discΓCodiscTriple C D).mono_leftToRight_app_iff_mono_adj₂_unit_app

instance [PiecesHavePoints C D] {X : D} : Mono ((sharp C D).η.app (disc.obj X)) := by
  exact (piecesHavePoints_iff_mono_sharp_unit_disc C D).1 ‹_› X

instance [PiecesHavePoints C D] : Mono (whiskerLeft (disc : D ⥤ C) (sharp C D).η) :=
  @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ <| (piecesHavePoints_iff_mono_sharp_unit_disc C D).1 ‹_›

end PiecesHavePoints

end Cohesive

end CategoryTheory
