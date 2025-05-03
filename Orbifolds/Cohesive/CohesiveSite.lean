import Orbifolds.Cohesive.Basic
import Orbifolds.ForMathlib.LocalSite
import Orbifolds.ForMathlib.LocallyConnectedSite

/-!
# Cohesive sites
Cohesive sites are sites with a number of useful properties that make their sheaf topos into
a cohesive topos. See https://ncatlab.org/nlab/show/cohesive+site.

Every cohesive site is in particular local and locally connected, and every cosifted category
with a terminal object that admits morphisms to every object is cohesive when equipped with
the trivial topology.

TODO: generalise universe levels from `max u v` to `max u v w` again once that is possible.
-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A cohesive site is a cosifted locally connected site with a terminal object that admits
morphisms to every other object. This guarantees that the sheaf topos is a cohesive topos. -/
class GrothendieckTopology.IsCohesiveSite extends J.IsLocallyConnectedSite, IsSifted Cᵒᵖ,
    HasTerminal C where
  /-- For every object `X : C` there is at least one morphism from the terminal object to `X`. -/
  nonempty_fromTerminal {X} : Nonempty (⊤_ C ⟶ X)

/-- Every cohesive site is in particular a local site. -/
instance [J.IsCohesiveSite] : J.IsLocalSite where
  eq_top_of_mem S hS := by
    rw [← S.id_mem_iff_eq_top]
    let ⟨f, hf⟩ := (IsLocallyConnectedSite.isConnected_of_mem S hS).is_nonempty
    let ⟨g⟩ := IsCohesiveSite.nonempty_fromTerminal (J := J) (X := f.left)
    exact terminal.hom_ext (𝟙 _) (g ≫ f.hom) ▸ S.downward_closed hf g

/-- Every cosifted category with a terminal object that admits morphisms to every other object
becomes a cohesive site when equipped with the trivial topology. -/
lemma isCohesiveSite_trivial {C : Type u} [Category.{v} C] [HasTerminal C] [IsSifted Cᵒᵖ]
    (h : ∀ X, Nonempty (⊤_ C ⟶ X)): (trivial C).IsCohesiveSite where
  nonempty_fromTerminal := h _

namespace Cohesive

-- TODO: figure out how to get rid of the `HasWeakSheafify` assumption.
variable [J.IsCohesiveSite] [HasWeakSheafify J (Type max u v)]

/-- The cohesive structure of the sheaf topos on a cohesive site. -/
noncomputable instance : CohesiveStructure (Sheaf J (Type max u v)) (Type max u v) where
  π₀ := _
  disc := _
  Γ := _
  codisc := _
  π₀DiscAdj := π₀ConstantSheafAdj.{u,v,max v} J
  discΓAdj := constantSheafΓAdj J _
  ΓCodiscAdj := ΓCoconstantSheafAdj J
  preservesFiniteProducts_π₀ := inferInstance
  fullyFaithfulDisc := fullyFaithfulConstantSheaf J
  fullyFaithfulCodisc := fullyFaithfulCoconstantSheaf J

lemma ΓCoconstantSheafAdj_unit_app {X : Sheaf J (Type max u v)} :
    (ΓCoconstantSheafAdj.{u,v} J).unit.app X = (by sorry) := by
  simp [ΓCoconstantSheafAdj, Adjunction.ofNatIsoLeft, Adjunction.homEquiv]
  simp [Adjunction.equivHomsetLeftOfNatIso]
  simp [ΓNatIsoSheafSections, sheafSectionsNatIsoEvaluation]
  sorry

lemma Sheaf.discToCodisc_app {X : (Type max u v)} :
    (discToCodisc (Sheaf J (Type max u v)) (Type max u v)).app X =
      ⟨inv (toSheafify J ((Functor.const _).obj X)) ≫ { app Y x y := ⟨x⟩ }⟩ := by
  rw [Cohesive.discToCodisc_app, IsIso.comp_inv_eq]
  apply Sheaf.hom_ext
  rw [instCategorySheaf_comp_val, Category.assoc, IsIso.eq_inv_comp]
  ext Y x
  dsimp
  simp [codisc, coconstantSheaf, Presheaf.coconst, discΓAdj, constantSheafΓAdj, ΓCodiscAdj]
  ext y
  simp [disc, Adjunction.equivHomsetLeftOfNatIso]
  simp? [ΓNatIsoSheafSections]
  sorry

/-- In sheaf topoi on cohesive sites, pieces have points in the sense that the components of
the canonical points-to-pieces transformation `Γ ⟶ π₀` are epic. -/
instance : PiecesHavePoints (Sheaf J (Type max u v)) (Type max u v) := by
  refine (piecesHavePoints_iff_mono_discToCodisc_app _ _).2 fun X ↦ ?_
  rw [Sheaf.discToCodisc_app]
  refine @Hom.mono_of_presheaf_mono _ _ J _ _ _ _ _ <| @mono_comp _ _ _ _ _ _ _ _ <|
    @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ fun Y ↦ (mono_iff_injective fun x y ↦ ULift.up x).2 ?_
  intro (x : X) (x' : X) h
  refine ULift.up_inj.1 (congrFun h ⟨?_⟩)
  exact Classical.choice (IsCohesiveSite.nonempty_fromTerminal (J := J))

end Cohesive
