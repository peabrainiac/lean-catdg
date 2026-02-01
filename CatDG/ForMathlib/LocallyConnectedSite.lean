import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Sifted
import Mathlib.CategoryTheory.Sites.GlobalSections
import CatDG.ForMathlib.Classifier

/-!
# Locally connected sites
Locally connected sites are sites for which all covering sieves are connected as subcategories
of the corresponding slice category. This is useful because it guarantees the existence of a
further left adjoint `π₀` of the constant sheaf functor, making sheaf topoi on locally connected
sites locally connected.

See https://ncatlab.org/nlab/show/locally+connected+site.

## Main definitions / results
* `J.IsLocallyConnectedSite`: typeclass stating that (C,J) is locally connected.
* Every trivial site is locally connected.
* `isSheaf_const_obj`: on locally connected sites, every constant presheaf is a sheaf.
* `Sheaf.π₀ J`: the connected components functor on locally connected sites, sending each sheaf
  to the colimit of its underlying presheaf.
* `π₀ConstantSheafAdj`: the adjunction between `π₀ J` and the constant sheaf functor. This shows
  that sheaf topoi on locally connected sites are locally connected.
* `uniqueπ₀Obj_of_isRepresentable`: `π₀` sends representable sheaves to singleton types, i.e.
  all representable sheaves are connected.
* On locally connected sites with a terminal object, `π₀` preserves the terminal object, i.e.
  the terminal sheaf is connected. This is enough to show that the sheaf topos is connected.
* On cosifted locally connected sites, `π₀` preserves all finite products, i.e. the sheaf topos
  is strongly connected. This is not yet sorry-free because it depends on a characterisation
  of sifted categories.
-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A locally connected site is a site with the property that every covering sieve is connected
as a full subcategory of the corresponding slice category. In particular, every covering sieve
is nonempty. -/
class GrothendieckTopology.IsLocallyConnectedSite where
  /-- Every covering sieve `S ∈ J X` is connected when interpreted as a full subcategory of the
  slice category `Over X`. -/
  isConnected_of_mem : ∀ {X}, ∀ S ∈ J X, IsConnected S.arrows.category

/-- Every category with a terminal object is nonempty.
TODO: add a similar instance for `HasInitial` and move both to another file. -/
instance [HasTerminal C] : Nonempty C := ⟨⊤_ C⟩

/-- Every category becomes a locally connected site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] : (trivial C).IsLocallyConnectedSite where
  isConnected_of_mem _ hS := @isConnected_of_hasTerminal _ _ <|
    @hasLimitsOfShape_of_closedUnderLimits _ _ _ _ _ ⟨fun _ _ ↦ trivial_covering.1 hS ▸ trivial⟩ _

variable [J.IsLocallyConnectedSite]

/-- On locally connected sites, every constant presheaf is a sheaf. -/
lemma isSheaf_const_obj {X : Type w} : Presheaf.IsSheaf J ((Functor.const _).obj X) := by
  refine (isSheaf_iff_isSheaf_of_type J _).2 fun Y S hS x hx ↦ ?_
  let ⟨f, hf⟩ := (IsLocallyConnectedSite.isConnected_of_mem S hS).is_nonempty
  refine ⟨@x f.left f.hom hf, ?_, ?_⟩
  · intro Z g hg
    have := IsLocallyConnectedSite.isConnected_of_mem S hS
    refine constant_of_preserves_morphisms (J := S.arrows.category)
      (fun f ↦ @x f.obj.left f.obj.hom f.property) ?_ ⟨f, hf⟩ ⟨.mk g, hg⟩
    intro f g h
    simpa using hx (𝟙 _) h.hom.left f.property g.property
  · intro x hx
    exact hx f.hom hf

/-- For constant presheaves on locally connected sites, `toSheafify` is an isomorphism.
TODO: remove `HasSheafify` instance. -/
instance {X : Type w} [HasWeakSheafify J (Type w)] :
    IsIso (toSheafify J ((Functor.const _).obj X)) :=
  isIso_toSheafify J (isSheaf_const_obj J)

/-- The connected components functor on sheaves of types on any local site, defined as taking
colimits of the underlying presheaves. -/
noncomputable def Sheaf.π₀ : Sheaf J (Type max u w) ⥤ Type max u w :=
  sheafToPresheaf J _ ⋙ colim

/-- The connected components functor on local sites is left-adjoint to the constant sheaf functor.
TODO: remove `HasSheafify` instance. -/
noncomputable def π₀ConstantSheafAdj [HasWeakSheafify J (Type max u w)] :
    Sheaf.π₀ J ⊣ constantSheaf J (Type max u w) := by
  refine colimConstAdj.restrictFullyFaithful (fullyFaithfulSheafToPresheaf J _) (.id _) ?_ ?_
  · exact (Functor.rightUnitor _).symm
  · refine ((Functor.leftUnitor _).trans ((Functor.rightUnitor _).symm.trans ?_)).trans
      (Functor.associator _ _ _).symm
    refine @asIso _ _ _ _ (Functor.whiskerLeft _ (toSheafification _ _)) ?_
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X ↦ isIso_toSheafify J <| isSheaf_const_obj J

/- A few lemmas for which I haven't found a better place yet.
TODO: clean up. -/
section TerminalSheaf

attribute [local instance] HasForget.hasCoeToSort
attribute [local instance] HasForget.instFunLike

/-- Morphisms to a terminal object are unique. -/
noncomputable def Limits.IsTerminal.uniqueHom {C : Type u} [Category.{v} C]
    {T : C} (hT : IsTerminal T) (X : C) : Unique (X ⟶ T) :=
  ⟨⟨hT.from X⟩, fun _ ↦ hT.hom_ext _ _⟩

/-- Terminal functors are represented by any terminal object. -/
noncomputable def Limits.IsTerminal.representableBy_isTerminal {C : Type u} [Category.{v} C]
    {F : Cᵒᵖ ⥤ Type w} (hF : IsTerminal F) {T : C} (hT : IsTerminal T) :
    F.RepresentableBy T where
  homEquiv {_} := @Equiv.ofUnique _ _ (hT.uniqueHom _) (hF.isTerminalObj_functor _).unique
  homEquiv_comp _ _ := ((hF.isTerminalObj_functor _).unique.instSubsingleton).elim _ _

/-- On categories with a terminal object, the terminal presheaf is representable. -/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : (⊤_ Cᵒᵖ ⥤ Type w).IsRepresentable :=
  (terminalIsTerminal.representableBy_isTerminal terminalIsTerminal).isRepresentable

/-- On sites with a terminal object, the terminal sheaf is representable. -/
instance Sheaf.isRepresentable_terminal {C : Type u} [Category.{v} C] [HasTerminal C]
    {J : GrothendieckTopology C} : (⊤_ Sheaf J (Type w)).val.IsRepresentable :=
  (terminalIsTerminal.isTerminalSheafVal.representableBy_isTerminal
    terminalIsTerminal).isRepresentable

/-- The colimit of any representable functor is a singleton type. -/
noncomputable def unique_colimit_representable {C : Type u} [Category.{v} C]
    (F : Cᵒᵖ ⥤ Type max u w) [F.IsRepresentable] : Unique (colimit F) :=
  @Equiv.unique _ _ {
    default := Quot.mk _ ⟨op F.reprX, F.reprx⟩
    uniq x := by
      refine x.out_eq.symm.trans (Quot.eq.2 (.symm _ _ <| .rel _ _ ⟨?_, ?_⟩))
      · exact (F.representableBy.homEquiv.symm x.out.2).op
      · exact .trans (by simp) (F.representableBy.homEquiv_comp _ _)
  } (Types.colimitEquivColimitType F)

end TerminalSheaf

/-- `Sheaf.π₀` sends representable sheaves to singleton types. -/
noncomputable def uniqueπ₀Obj_of_isRepresentable (X : Sheaf J (Type max u w))
    [X.val.IsRepresentable] : Unique ((π₀ J).obj X) :=
  unique_colimit_representable X.val

/-- On locally connected sites with a terminal object, `Sheaf.π₀` preserves the terminal object. -/
instance [HasTerminal C] : PreservesLimit (Functor.empty.{0} _) (π₀.{u,v,w} J) := by
  refine preservesTerminal_of_iso _ (IsTerminal.uniqueUpToIso ?_ terminalIsTerminal)
  exact (Types.isTerminalEquivUnique _).2 <| uniqueπ₀Obj_of_isRepresentable _ _

/-- If `C` is sifted, the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products.
Taken from mathlib PR #17781.
TODO: generalise the universe levels of `IsSifted.colim_preservesFiniteProducts_of_isSifted` so it
can replace this. -/
instance colimPreservesFiniteProductsOfIsSifted {C : Type u} [Category.{v} C] :
    PreservesFiniteProducts (colim : (C ⥤ _) ⥤ Type max u w) := by
  sorry

/-- Sheaf topoi on cosifted locally connected sites are strongly connected, in the sense that
`π₀` preserves all finite products.
TODO: generalise universe levels. -/
instance [IsSifted Cᵒᵖ] :
    PreservesFiniteProducts (π₀.{u,v,w} J) :=
  comp_preservesFiniteProducts _ _
