import Orbifolds.ForMathlib.LocalSite

universe u v w u₂ v₂ w₂

open CategoryTheory Limits Sheaf Opposite

namespace CategoryTheory

attribute [local instance] ConcreteCategory.hasCoeToSort
attribute [local instance] ConcreteCategory.instFunLike

variable {C : Type u} [Category.{v} C]

/-- A presieve `S` on `X` in a concrete category is jointly surjective if every `x : X` is in
  the image of some `f` in `S`. -/
def Presieve.IsJointlySurjective [ConcreteCategory.{w} C] {X : C} (S : Presieve X) : Prop :=
  ∀ x : X, ∃ Y, ∃ f ∈ @S Y, ∃ y, f y = x

lemma Presieve.isJointlySurjective_iff_iUnion_range_eq_univ [ConcreteCategory.{w} C]
    {X : C} {S : Presieve X} : IsJointlySurjective S ↔
    ⋃ (Y : C) (f ∈ @S Y), Set.range f = Set.univ := by
  simp [IsJointlySurjective, Set.iUnion_eq_univ_iff]

/-- A site is concrete if it is a concrete category in such a way that points correspond to
  morphisms from a terminal object, and all sieves are jointly surjective. -/
class ConcreteSite (J : GrothendieckTopology C)
    extends HasTerminal C, ConcreteCategory.{v} C where
  /-- The forgetful functor is given by morphisms from the terminal object. Since a forgetful
    functor might already exists, this is encoded here as a natural isomorphism. -/
  forget_natIso_coyoneda : (CategoryTheory.forget C) ≅ coyoneda.obj (.op (⊤_ C))
  /-- Said isomorphism takes `x : X` to a morphism with underlying map `fun _ ↦ x`. -/
  forget_natIso_coyoneda_apply {X : C} {x : X} :
    (DFunLike.coe (F := ⊤_ C ⟶ X) <| forget_natIso_coyoneda.hom.app X x) = fun _ ↦ x
  /-- All covering sieves are jointly surjective. -/
  sieves_isJointlySurjective {X : C} {S : Sieve X} :
    S ∈ J.sieves X → S.arrows.IsJointlySurjective

/-- The terminal object of a concrete site has exactly one point. -/
noncomputable instance ConcreteSite.instUniqueTerminal (J : GrothendieckTopology C) [ConcreteSite J] :
    Unique (⊤_ C) :=
  (forget_natIso_coyoneda.app (⊤_ C)).toEquiv.unique (β := ⊤_ C ⟶ ⊤_ C)

/-- Every concrete site is also a local site. -/
instance (J : GrothendieckTopology C) [ConcreteSite J] : LocalSite J where
  eq_top_of_mem S hS := (S.id_mem_iff_eq_top).1 <| by
    let ⟨Y, f, hf, y, hfy⟩ := ConcreteSite.sieves_isJointlySurjective hS default
    let y' : ⊤_ C ⟶ Y := ConcreteSite.forget_natIso_coyoneda.hom.app Y  y
    convert S.downward_closed hf y'
    exact Subsingleton.elim _ _

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
