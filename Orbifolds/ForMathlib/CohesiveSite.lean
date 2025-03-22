import Orbifolds.ForMathlib.LocalSite
import Orbifolds.ForMathlib.LocallyConnectedSite

/-!
# Cohesive sites
Cohesive sites are sites with a number of useful properties that make their sheaf topos into
a cohesive topos. See https://ncatlab.org/nlab/show/cohesive+site.

Every cohesive site is in particular local and locally connected, and every cosifted category
with a terminal object that admits morphisms to every object is cohesive when equipped with
the trivial topology.
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
instance [J.IsCohesiveSite] : LocalSite J where
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
variable [J.IsCohesiveSite] [HasWeakSheafify J (Type max u v w)]

/-- The shape modality of the sheaf topos of a cohesive site.
TODO: generalise to arbitrary cohesive topoi once those are defined. -/
noncomputable def shape : Monad (Sheaf J (Type max u v w)) :=
    (π₀ConstantSheafAdj.{u,v,max v w} J).toMonad

/-- The flat modality of the sheaf topos of a cohesive site.
TODO: generalise to arbitrary cohesive topoi once those are defined. -/
noncomputable def flat : Comonad (Sheaf J (Type max u v w)) :=
    (constantSheafΓAdj.{u,v} J (Type max u v w)).toComonad

/-- The sharp modality of the sheaf topos of a cohesive site.
TODO: generalise to arbitrary cohesive topoi once those are defined. -/
noncomputable def sharp : Monad (Sheaf J (Type max u v w)) :=
    (ΓCodiscAdj.{u,v,w} J).toMonad

/-- The points-to-pieces transformation of the sheaf topos of a cohesive site.
TODO: generalise to arbitrary cohesive topoi once those are defined. -/
noncomputable def pointsToPieces : (flat J).toFunctor ⟶ (shape J).toFunctor :=
  (flat J).ε ≫ (shape J).η

noncomputable def pointsToPiecesNatIso : pointsToPieces J =
    whiskerRight ((Functor.rightUnitor _).inv ≫
        whiskerLeft _ (constantSheafΓAdj J _).unit ≫
        (Functor.associator _ _ _).inv ≫ whiskerRight (pointsToPieces J) _ ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft _ (asIso (constantSheafΓAdj J _).unit).inv ≫
        (Functor.rightUnitor _).hom) (constantSheaf J _) := by
  sorry

/--  Sheaf topoi on cohesive sites have the property that "pieces have points" in the sense
that `pointsToPieces J` is an epimorphism. -/
lemma epi_pointsToPieces : Epi (pointsToPieces J) := by
  refine (NatTrans.epi_iff_epi_app _).2 fun X ↦ ?_
  refine Hom.epi_of_presheaf_epi J _ _ (h := (NatTrans.epi_iff_epi_app _).2 fun Y ↦ ?_)
  rw [epi_iff_surjective]
  /-dsimp [pointsToPieces, shape, flat, π₀ConstantSheafAdj, constantSheafΓAdj,
    Adjunction.restrictFullyFaithful, Functor.FullyFaithful.id,
    Functor.FullyFaithful.homEquiv, Adjunction.homEquiv, colimConstAdj]
  simp only [Category.comp_id, Category.id_comp]
  simp?-/
  sorry

end Cohesive
