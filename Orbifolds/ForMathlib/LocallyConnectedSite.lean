import Mathlib.CategoryTheory.Limits.FullSubcategory
import Orbifolds.ForMathlib.GlobalSections

/-!
# Locally connected sites
See https://ncatlab.org/nlab/show/locally+connected+site.
-/

universe u v w

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A locally connected site is a site with the property that every covering sieve is connected
as a full subcategory of the corresponding slice category. In particular, every covering sieve
is nonempty. -/
class GrothendieckTopology.IsLocallyConnectedSite where
  /-- Every covering sieve `S ∈ J X` is connected when interpreted as a full subcategory of the
  slice category `Over X`. -/
  isConnected_of_mem : ∀ {X}, ∀ S ∈ J X,
    IsConnected (FullSubcategory fun f : Over X ↦ S.arrows f.hom)

/-- Every category with a terminal object is nonempty.
TODO: add a similar instance for `HasInitial` and move both to another file. -/
instance [HasTerminal C] : Nonempty C := ⟨⊤_ C⟩

/-- Every category with a terminal object is connected.
TODO: add a similar instance for `HasInitial` and move both to another file. -/
instance isConnected_of_hasTerminal [HasTerminal C] : IsConnected C :=
  zigzag_isConnected fun X Y ↦ .of_hom_inv (terminal.from X) (terminal.from Y)

/-- Every category becomes a locally connected site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] : (trivial C).IsLocallyConnectedSite where
  isConnected_of_mem S hS := by
    refine @isConnected_of_hasTerminal _ _ ?_
    exact hasLimitsOfShape_of_closedUnderLimits fun _ _ _ _ ↦ trivial_covering.1 hS ▸ trivial

variable [J.IsLocallyConnectedSite]

/-- On locally connected sites, every constant presheaf is a sheaf. -/
lemma isSheaf_const_obj {X : Type max u w} : Presheaf.IsSheaf J ((Functor.const _).obj X) := by
  refine (isSheaf_iff_isSheaf_of_type J _).2 fun Y S hS x hx ↦ ?_
  let ⟨f, hf⟩ := (IsLocallyConnectedSite.isConnected_of_mem S hS).is_nonempty
  refine ⟨@x f.left f.hom hf, ?_, ?_⟩
  · intro Z g hg
    have := IsLocallyConnectedSite.isConnected_of_mem S hS
    refine constant_of_preserves_morphisms (J := FullSubcategory fun f : Over Y ↦ S.arrows f.hom)
      (fun f ↦ @x f.obj.left f.obj.hom f.property) ?_ ⟨f, hf⟩ ⟨.mk g, hg⟩
    intro f g h
    simpa using hx (𝟙 _) h.left f.property g.property
  · intro x hx
    exact hx f.hom hf

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
    refine @asIso _ _ _ _ (whiskerLeft _ (toSheafification _ _)) ?_
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X ↦ isIso_toSheafify J <| isSheaf_const_obj J
