import Mathlib.CategoryTheory.Sites.DenseSubSite.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts

universe u v w u₂ v₂ w₂

open CategoryTheory Limits Sheaf

namespace CategoryTheory

/-- An explicit choice of terminal object in `C`.
  TODO: integrate this into `Mathlib.CategoryTheory.ChosenFiniteProducts`. -/
class ChosenTerminal (C : Type u) [Category.{v} C] where
  /-- A choice of a terminal object. -/
  terminal : LimitCone (Functor.empty.{0} C)

namespace ChosenTerminal

instance (C : Type u) [Category.{v} C] [ChosenTerminal C] : HasTerminal C where
  has_limit _ := @hasLimitOfIso _ _ _ _ _ _ ⟨⟨terminal⟩⟩ (Functor.uniqueFromEmpty _).symm

end ChosenTerminal

attribute [local instance] ConcreteCategory.hasCoeToSort
attribute [local instance] ConcreteCategory.instFunLike

variable {C : Type u} [Category.{v} C]

/-- A presieve `S` on `X` in a concrete category is jointly surjective if every `x : X` is in
  the image of some `f` in `S`. -/
def Presieve.IsJointlySurjective [ConcreteCategory.{w} C] {X : C} (S : Presieve X) : Prop :=
  ∀ x : X, ∃ (Y : C), ∃ f ∈ @S Y, ∃ y, f y = x

lemma Presieve.isJointlySurjective_iff_iUnion_range_eq_univ [ConcreteCategory.{w} C]
    {X : C} {S : Presieve X} : IsJointlySurjective S ↔
    ⋃ (Y : C) (f ∈ @S Y), Set.range f = Set.univ := by
  simp [IsJointlySurjective, Set.iUnion_eq_univ_iff]

/-- A site is concrete if it is a concrete category in such a way that points correspond to
  morphisms from a terminal object, and all sieves are jointly surjective. -/
class ConcreteSite (J : GrothendieckTopology C)
    extends ChosenTerminal C, ConcreteCategory.{v} C where
  forget_natIso_coyoneda : (CategoryTheory.forget C) ≅ coyoneda.obj (.op (⊤_ C))
  sieves_isJointlySurjective {X : C} (S : J.sieves X) : S.1.arrows.IsJointlySurjective

variable (J : GrothendieckTopology C) [ConcreteSite J]

def Presheaf.IsConcrete (P :  Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ X : C, Function.Injective fun p : P.obj (.op X) ↦ fun f : (⊤_ C ⟶ X) ↦ P.map (.op f) p

/-- The category of concrete sheaves. -/
structure ConcreteSheaf extends Sheaf J (Type w) where
  concrete : Presheaf.IsConcrete J val

/-- Morphisms of concrete sheaves are simply morphisms of sheaves. -/
instance : Category (ConcreteSheaf J) :=
  InducedCategory.category ConcreteSheaf.toSheaf

/-- The forgetful functor from concrete sheaves to sheaves. -/
def concreteSheafToSheaf : ConcreteSheaf J ⥤ Sheaf J (Type w) :=
  inducedFunctor _

def fullyFaithfulConcreteSheafToSheaf : (concreteSheafToSheaf J).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (concreteSheafToSheaf J).Full :=
  (fullyFaithfulInducedFunctor _).full

instance : (concreteSheafToSheaf J).Faithful :=
  (fullyFaithfulInducedFunctor _).faithful

end CategoryTheory
