import CatDG.ForMathlib.LocalSite
import CatDG.ForMathlib.BiseparatedPresheaf

/-!
# Concrete sites

Concrete sites are concrete categories whose forgetful functor is corepresented by a terminal
object, equipped with a Grothendieck topology consisting only of jointly surjective sieves.
See https://ncatlab.org/nlab/show/concrete+site.

Also see https://arxiv.org/abs/0807.1704; note that while that article requires concrete sites
to be subcanonical, we don't require that here.

## Main definitions / results:
* `Presieve.IsJointlySurjective`: property stating that a presieve in a concrete category is
  jointly surjective
* `IsConcreteSite`: typeclass giving a site the structure of a concrete site
* `IsConcreteSite.isLocalSite`: every concrete site is also a local site
* `IsConcreteSite.isSeparated_of_isRepresentable`: every representable presheaf on a concrete site
  is separated. In particular, to show that a concrete site is subcanonical it suffices to show
  the existence part of the sheaf condition for representable sheaves.

There is also some material on concrete sheaves, but they should probably be redefined in terms of
local sites / biseparated sheaves before being expanded upon.

## TODOs
* switch from `HasForget` to the new `ConcreteCategory` API
* maybe split out concrete categories where points correspond to morphisms from a terminal object
  into a separate definition / file
-/

universe u v w u₂ v₂ w₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

attribute [local instance] HasForget.hasCoeToSort
attribute [local instance] HasForget.instFunLike

variable {C : Type u} [Category.{v} C]

namespace Presieve

variable [HasForget.{w} C] {X : C}

/-- A presieve `S` on `X` in a concrete category is jointly surjective if every `x : X` is in
the image of some `f` in `S`. -/
def IsJointlySurjective (S : Presieve X) : Prop :=
  ∀ x : X, ∃ Y, ∃ f ∈ S (Y := Y), ∃ y, f y = x

lemma isJointlySurjective_iff_iUnion_range_eq_univ {S : Presieve X} :
    IsJointlySurjective S ↔ ⋃ (Y : C) (f ∈ S (Y := Y)), Set.range f = Set.univ := by
  simp [IsJointlySurjective, Set.iUnion_eq_univ_iff]

lemma IsJointlySurjective.iUnion_eq_univ {S : Presieve X} (hS : S.IsJointlySurjective) :
    ⋃ (Y : C) (f ∈ S (Y := Y)), Set.range f = Set.univ :=
  isJointlySurjective_iff_iUnion_range_eq_univ.1 hS

lemma IsJointlySurjective.mono {S R : Presieve X} (hR : S ≤ R) (hS : S.IsJointlySurjective) :
    R.IsJointlySurjective :=
  forall_imp (fun _ ↦ .imp fun _ ↦ .imp fun _ ↦ And.imp_left fun _ ↦ hR _ ‹_›) hS

end Presieve

/-- A site is concrete if it is a concrete category in such a way that points correspond to
morphisms from a terminal object, and all sieves are jointly surjective. -/
class GrothendieckTopology.IsConcreteSite (J : GrothendieckTopology C)
    extends HasTerminal C, HasForget.{v} C where
  /-- The forgetful functor is given by morphisms from the terminal object. Since a forgetful
  functor might already exists, this is encoded here as a natural isomorphism. -/
  forgetNatIsoCoyoneda : (CategoryTheory.forget C) ≅ coyoneda.obj (.op (⊤_ C))
  /-- Said isomorphism takes `x : X` to a morphism with underlying map `fun _ ↦ x`. -/
  forgetNatIsoCoyoneda_apply {X : C} {x : X} :
    (DFunLike.coe (F := ⊤_ C ⟶ X) <| forgetNatIsoCoyoneda.hom.app X x) = fun _ ↦ x
  /-- All covering sieves are jointly surjective. -/
  isJointlySurjective_of_mem {X : C} {S : Sieve X} (hS : S ∈ J X) : S.arrows.IsJointlySurjective

namespace GrothendieckTopology.IsConcreteSite

lemma coyoneda_obj_terminal_faithful (J : GrothendieckTopology C) [J.IsConcreteSite] :
    (coyoneda.obj (.op (⊤_ C))).Faithful :=
  .of_iso (forgetNatIsoCoyoneda (J := J))

/-- The terminal object of a concrete site has exactly one point. -/
noncomputable instance instUniqueTerminal
    (J : GrothendieckTopology C) [J.IsConcreteSite] : Unique (⊤_ C) :=
  (forgetNatIsoCoyoneda.app (⊤_ C)).toEquiv.unique (β := ⊤_ C ⟶ ⊤_ C)

/-- Every concrete site is also a local site. -/
instance isLocalSite (J : GrothendieckTopology C) [J.IsConcreteSite] : J.IsLocalSite where
  eq_top_of_mem S hS := (S.id_mem_iff_eq_top).1 <| by
    let ⟨Y, f, hf, y, hfy⟩ := IsConcreteSite.isJointlySurjective_of_mem hS default
    let y' : ⊤_ C ⟶ Y := IsConcreteSite.forgetNatIsoCoyoneda.hom.app Y  y
    convert S.downward_closed hf y'
    exact Subsingleton.elim _ _

/-- On concrete sites, covering sieves contain all morphisms from the terminal object. -/
lemma from_terminal_mem_of_mem (J : GrothendieckTopology C) [J.IsConcreteSite] {X : C} {S : Sieve X}
    (hS : S ∈ J X) (f : ⊤_ C ⟶ X) : S f := by
  let ⟨Y, f, hf, y, hy⟩ := isJointlySurjective_of_mem hS (f default)
  convert Sieve.downward_closed S hf (forgetNatIsoCoyoneda.hom.app _ y)
  apply (forget C).map_injective; ext x
  rw [Unique.eq_default x, FunctorToTypes.map_comp_apply]
  exact hy.symm.trans <| congrArg _ <| congrFun forgetNatIsoCoyoneda_apply.symm default

lemma isSeparated_yoneda_obj (J : GrothendieckTopology C) [J.IsConcreteSite] (X : C) :
    Presieve.IsSeparated J (yoneda.obj X) := by
  intro Y S hS t (f : Y ⟶ X) (g : Y ⟶ X) hf hg
  have _ := coyoneda_obj_terminal_faithful J
  apply (coyoneda.obj (.op (⊤_ C))).map_injective; ext (y : ⊤_ C ⟶ _)
  exact (hf y (from_terminal_mem_of_mem J hS y)).trans (hg y (from_terminal_mem_of_mem J hS y)).symm

/-- Every representable presheaf on a concrete site is, while not necessarily a sheaf,
at least separated. -/
lemma isSeparated_of_isRepresentable (J : GrothendieckTopology C) [J.IsConcreteSite]
    (F : Cᵒᵖ ⥤ Type v) [F.IsRepresentable] : Presieve.IsSeparated J F :=
  Presieve.isSeparated_iso J F.reprW <| isSeparated_yoneda_obj J _

end GrothendieckTopology.IsConcreteSite

variable (J : GrothendieckTopology C) [J.IsConcreteSite]

def Presheaf.IsConcrete (P :  Cᵒᵖ ⥤ Type w) : Prop :=
  ∀ X : C, Function.Injective fun p : P.obj (.op X) ↦ fun f : (⊤_ C ⟶ X) ↦ P.map (.op f) p

/-- The category of concrete sheaves. -/
structure ConcreteSheaf extends Sheaf J (Type w) where
  concrete : Presheaf.IsConcrete J val

/-- Morphisms of concrete sheaves are simply morphisms of sheaves. -/
instance : Category (ConcreteSheaf J) :=
  InducedCategory.instCategory (F := ConcreteSheaf.toSheaf)

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
