import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Sites.LeftExact
import Orbifolds.ForMathlib.Classifier

/-!
# Biseparated presheaves
On any category with a two Grothendieck topologies `J` and `K`, we define the category `Bisep J K`
of all presheaves that are sheaves with respect to `J` and separated with respect to `K`, and show
that it is a reflective subcategory (TODO). Important examples (though not worked out in this file)
are the categories of diffeological spaces, quasitopological spaces and simplicial complexes.

See https://ncatlab.org/nlab/show/separated+presheaf#biseparated_presheaf and section C.2.2 of
*Sketches of an Elephant*.
-/

universe u v w u₂ v₂

open CategoryTheory Category Sheaf GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J K : GrothendieckTopology C)

/-- The category of biseparated presheaves with respect to `J` and `K`, i.e. of all presheaves that
are sheaves with respect to `J` and separated with respect to `K`. -/
structure Bisep where
  /-- The underlying presheaf. -/
  val : Cᵒᵖ ⥤ Type w
  /-- The underlying presheaf is a sheaf with respect to `J`. -/
  isSheaf : Presheaf.IsSheaf J val
  /-- The underlying presheaf is separated with respect to `K`. -/
  isSeparated : Presieve.IsSeparated K val

variable {J K}

/-- Morphisms of biseparated presheaves are just morphisms of their underlying presheaves. -/
@[ext]
structure Bisep.Hom (X Y : Bisep J K) where
  /-- The underlying morphism of presheaves. -/
  val : X.val ⟶ Y.val

@[simps id_val comp_val]
instance Bisep.instCategory : Category (Bisep J K) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩
  id_comp _ := Hom.ext <| id_comp _
  comp_id _ := Hom.ext <| comp_id _
  assoc _ _ _ := Hom.ext <| assoc _ _ _

/-- The sheaf (with respect to `J`) underlying a biseparated presheaf. -/
@[simps]
def Bisep.toSheaf (P : Bisep J K) : Sheaf J (Type w) := ⟨P.val, P.isSheaf⟩

variable (J K) in
/-- The inclusion functor from biseparated presheaves to sheaves. -/
@[simps]
def bisepToSheaf : Bisep J K ⥤ Sheaf J (Type w) where
  obj P := P.toSheaf
  map f := ⟨f.val⟩

variable (J K) in
/-- The inclusion functor from biseparated presheaves to sheaves is fully faithful. -/
def fullyFaithfulBisepToSheaf : (bisepToSheaf J K).FullyFaithful where
  preimage f := ⟨f.val⟩

instance : (bisepToSheaf J K).Full :=
  (fullyFaithfulBisepToSheaf J K).full

instance : (bisepToSheaf J K).Faithful :=
  (fullyFaithfulBisepToSheaf J K).faithful

instance : (bisepToSheaf J K).ReflectsIsomorphisms :=
  (fullyFaithfulBisepToSheaf J K).reflectsIsomorphisms

-- this is currently needed to obtain the instance `HasSheafify J (Type max u v)`.
attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

noncomputable def Sheaf.toExpΩ' (h : J ≤ K) (X : Sheaf J (Type max u v)) : X ⟶ X ⟹ J.Ω' h :=
  CartesianClosed.curry (J.classifier.χ <| CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) ≫
    (exp X).map (J.ΩProjectionOfLE h)

/-- Subpresheaves of separated presheaves are themselves separated. -/
lemma Subpresheaf.isSeparated_toPresheaf {C : Type u} [Category.{v, u} C]
    {J : GrothendieckTopology C} {F : Functor Cᵒᵖ (Type w)} (G : Subpresheaf F)
    (h : Presieve.IsSeparated J F) : Presieve.IsSeparated J G.toPresheaf := by
  intro X S hS x _ _ hx₁ hx₂
  exact Subtype.ext <| h S hS _ _ _ (hx₁.compPresheafMap G.ι) (hx₂.compPresheafMap G.ι)

open MonoidalCategory in
/-- A more concrete choice of exponential object in presheaf categories. -/
@[simps]
def Functor.chosenExp {C : Type u} [Category.{v} C] (F G : Cᵒᵖ ⥤ Type max u v) :
    Cᵒᵖ ⥤ Type max u v where
  obj X := F ⊗ uliftYoneda.obj X.unop ⟶ G
  map f g := F ◁ uliftYoneda.map f.unop ≫ g

lemma uliftYonedaEquiv_naturality_symm {C : Type u} [Category.{v} C] {X Y : Cᵒᵖ}
    {F : Cᵒᵖ ⥤ Type max w v} (x : F.obj X) (f : X ⟶ Y) :
    uliftYonedaEquiv.symm (F.map f x) = uliftYoneda.map f.unop ≫ uliftYonedaEquiv.symm x := by
  simpa using (congrArg uliftYonedaEquiv.symm <|
    uliftYonedaEquiv_naturality (uliftYonedaEquiv.symm x) f:)

/-- Isomorphism witnessing that in presheaf categories, exponential objects are indeed isomorphic
to `Functor.chosenExp`. -/
noncomputable def Functor.expObjIsoChosenExp {C : Type u} [Category.{v} C]
    (F G : Cᵒᵖ ⥤ Type max u v) : F ⟹ G ≅ F.chosenExp G :=
  NatIso.ofComponents (fun X ↦ {
    hom x := CartesianClosed.uncurry <| uliftYonedaEquiv.symm x
    inv f := uliftYonedaEquiv <| CartesianClosed.curry f
  }) fun f ↦ funext fun x ↦ (congrArg CartesianClosed.uncurry <|
    uliftYonedaEquiv_naturality_symm x f).trans <| CartesianClosed.uncurry_natural_left _ _

/-- The property of being separated for some presieve is preserved under isomorphisms.
TODO: upstream to mathlib. -/
theorem Presieve.isSeparatedFor_iso {C : Type u} [Category.{v} C]
    {F F' : Cᵒᵖ ⥤ Type w} (i : F ≅ F') {X : C} {R : Presieve X} (hF : R.IsSeparatedFor F) :
    R.IsSeparatedFor F' := by
  intro x t₁ t₂ ht₁ ht₂
  simpa using congrArg (i.hom.app _) <| hF (x.compPresheafMap i.inv) _ _
    (ht₁.compPresheafMap i.inv) (ht₂.compPresheafMap i.inv)

/-- The property of being separated is preserved under isomorphisms.
TODO: upstream to mathlib. -/
theorem Presieve.isSeparated_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F F' : Cᵒᵖ ⥤ Type w} (i : F ≅ F')
    (hF : Presieve.IsSeparated J F) : Presieve.IsSeparated J F' :=
  fun S hS ↦ Presieve.isSeparatedFor_iso i (hF S hS)

open MonoidalCategory in
example {C : Type u} [Category.{v} C] {F G : Cᵒᵖ ⥤ Type max w v} (f : F ⟶ G)
    (H : Cᵒᵖ ⥤ Type max w v) (X : Cᵒᵖ) : (f ▷ H).app X = Prod.map (f.app X) id := by
  rfl

open CartesianClosed Opposite MonoidalCategory in
lemma Presieve.IsSeparated.exp {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type max u v} (hF : IsSeparated J F) (G : Cᵒᵖ ⥤ Type max u v) :
    IsSeparated J (G ⟹ F) := by
  /-intro X S hS x x₁ x₂ hx₁ hx₂
  refine uliftYonedaEquiv.{u,v,u}.symm.injective <| uncurry_injective ?_
  ext Y ⟨y, ⟨(f : _ ⟶ _)⟩⟩
  refine (hF _ <| J.pullback_stable f hS).ext fun Z g hg ↦ ?_
  refine ((congrFun ((uncurry (uliftYonedaEquiv.symm x₁)).naturality g.op).symm _).trans ?_).trans
    (congrFun ((uncurry (uliftYonedaEquiv.symm x₂)).naturality g.op) _)
  dsimp [uliftYoneda]
  have h := (hx₁ _ hg).trans (hx₂ _ hg).symm
  replace h := (uliftYonedaEquiv_naturality_symm x₁ (g ≫ f).op).symm.trans <|
    (congrArg _ h).trans <| uliftYonedaEquiv_naturality_symm x₂ (g ≫ f).op
  replace h := (uncurry_natural_left _ _).symm.trans <| (congrArg uncurry h).trans <|
    uncurry_natural_left _ _
  have h' := congrFun (NatTrans.congr_app h _) ⟨G.map g.op y, ⟨𝟙 _⟩⟩
  simp at h'-/
  refine isSeparated_iso J (G.expObjIsoChosenExp F).symm ?_
  intro X S hS x x₁ x₂ hx₁ hx₂
  dsimp
  ext Y ⟨y, ⟨(f : _ ⟶ _)⟩⟩
  refine (hF _ <| J.pullback_stable f hS).ext fun Z g hg ↦ ?_
  refine ((congrFun (x₁.naturality g.op).symm _).trans ?_).trans (congrFun (x₂.naturality g.op) _)
  have h := congrFun (NatTrans.congr_app ((hx₁ _ hg).trans (hx₂ _ hg).symm) _) ⟨G.map g.op y, ⟨𝟙 _⟩⟩
  refine (congrArg (x₁.app _) ?_).trans <| h.trans <| congrArg (x₂.app _) <| Eq.symm ?_
  all_goals exact Prod.ext rfl <| ULift.ext _ _ (id_comp _).symm

lemma Presheaf.IsSheaf.exp {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u₂}
    [Category.{v₂} A] [HasSheafify J A] [CartesianMonoidalCategory A] [CartesianClosed (Cᵒᵖ ⥤ A)]
    {F : Cᵒᵖ ⥤ A} (hF : IsSheaf J F) (G : Cᵒᵖ ⥤ A) : IsSheaf J (G ⟹ F) :=
  (Presheaf.isSheaf_of_iso_iff <| Classical.choice (ExponentialIdeal.exp_closed
    (i := sheafToPresheaf J A) ⟨⟨F, hF⟩, ⟨Iso.refl _⟩⟩ G).choose_spec).1 (Sheaf.cond _)

-- TODO: move to `Mathlib.CategoryTheory.Sites.Sheaf`
lemma Presieve.isSeparated_of_le {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ Type w}
    {J K : GrothendieckTopology C} (h : J ≤ K) (hP : Presieve.IsSeparated K P) :
    Presieve.IsSeparated J P :=
  fun S hS ↦ hP S <| h _ hS

variable (J K) in
noncomputable def sheafToBisep : Sheaf J (Type max u v) ⥤ Bisep J K where
  obj X := {
    val := _
    isSheaf := cond <| image <| X.toExpΩ' (le_sup_left (b := K))
    isSeparated := Subpresheaf.isSeparated_toPresheaf _ <| by
      have h : Presieve.IsSeparated K (X.1 ⟹ (J.Ω' (le_sup_left (b := K))).1) := by
        refine Presieve.IsSeparated.exp (Presieve.isSeparated_of_isSheaf _ _ ?_) _
        exact (isSheaf_iff_isSheaf_of_type _ _).1 <| Presheaf.isSheaf_of_le le_sup_right (J ⊔ K).Ω.2
      exact fun {_} ↦ Presieve.isSeparated_iso K
        (isoSheafify _ <| Presheaf.IsSheaf.exp (Sheaf.cond _) _) h
  }
  map {X Y} f := ⟨{
    app Z := by
      simp
      sorry
  }⟩

end CategoryTheory
