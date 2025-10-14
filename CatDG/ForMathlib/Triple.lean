import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
Lemmas that should go into `Mathlib.CategoryTheory.Adjunction.Triple`.
-/

open CategoryTheory Limits

namespace CategoryTheory.Adjunction.Triple

variable {C D : Type*} [Category C] [Category D] {F H : C ⥤ D} {G : D ⥤ C} (t : Triple F G H)

section InnerFullyFaithful

variable [G.Full] [G.Faithful]

omit [G.Full] [G.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the unit of the first adjunction under `H`. -/
lemma homEquiv_counit_unit_app_eq_H_map_unit {X : C} :
    t.adj₂.homEquiv _ _ (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) = H.map (t.adj₁.unit.app X) := by
  simp [Adjunction.homEquiv_apply]

omit [G.Full] [G.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the counit of the second adjunction under `F`. -/
lemma homEquiv_symm_counit_unit_app_eq_F_map_counit {X : C} :
    (t.adj₁.homEquiv _ _).symm (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) =
    F.map (t.adj₂.counit.app X) := by
  simp [Adjunction.homEquiv_symm_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the components of the natural
transformation `H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are simply
the images of the components of the natural transformation `H ⟶ F` under `G`. -/
lemma counit_unit_app_eq_map_HToF {X : C} :
    t.adj₂.counit.app X ≫ t.adj₁.unit.app X = G.map (t.rightToLeft.app X) := by
  refine ((t.adj₂.homEquiv _ _).symm_apply_apply _).symm.trans ?_
  rw [homEquiv_counit_unit_app_eq_H_map_unit]; dsimp
  rw [Adjunction.homEquiv_symm_apply, ← Adjunction.inv_map_unit, ← G.map_inv,
    ← G.map_comp, t.rightToLeft_eq_units]
  simp

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful and its codomain has
all pushouts, the natural transformation `H ⟶ F` is epic iff the unit of the adjunction `F ⊣ G`
whiskered with `H` is. -/
lemma epi_rightToLeft_iff_epi_whiskerRight_adj₁_unit [HasPushouts D] :
    Epi t.rightToLeft ↔ Epi (Functor.whiskerRight t.adj₁.unit H) := by
  repeat rw [NatTrans.epi_iff_epi_app]
  exact forall_congr' fun _ ↦ t.epi_rightToLeft_app_iff_epi_map_adj₁_unit_app

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, `H` preserves epimorphisms
(which is for example the case if `H` has a further right adjoint) and both categories have
all pushouts, the natural transformation `H ⟶ F` is epic iff the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions is. -/
lemma epi_rightToLeft_iff [HasPushouts C] [HasPushouts D] [H.PreservesEpimorphisms] :
    Epi t.rightToLeft ↔ Epi (t.adj₂.counit ≫ t.adj₁.unit) := by
  repeat rw [NatTrans.epi_iff_epi_app]
  exact forall_congr' fun _ ↦ t.epi_rightToLeft_app_iff

end InnerFullyFaithful

section OuterFullyFaithful

variable [F.Full] [F.Faithful]

omit [F.Full] [F.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the unit of the second adjunction under `G`. -/
lemma homEquiv_counit_unit_app_eq_G_map_unit {X : D} :
    t.adj₁.homEquiv _ _ (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) = G.map (t.adj₂.unit.app X) := by
  simp [homEquiv_apply]

omit [F.Full] [F.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the counit of the first adjunction under `G`. -/
lemma homEquiv_symm_counit_unit_app_eq_G_map_counit {X : D} :
    (t.adj₂.homEquiv _ _).symm (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) =
    G.map (t.adj₁.counit.app X) := by
  simp [homEquiv_symm_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions
are simply the components of the natural transformation `F ⟶ H` at `G`. -/
lemma counit_unit_app_eq_FToH_app {X : D} :
    t.adj₁.counit.app X ≫ t.adj₂.unit.app X = t.leftToRight.app (G.obj X) := by
  refine ((t.adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_
  rw [homEquiv_symm_counit_unit_app_eq_G_map_counit, t.adj₂.homEquiv_apply, t.leftToRight_app,
    ← H.map_inv]
  congr
  exact IsIso.eq_inv_of_hom_inv_id (t.adj₁.right_triangle_components _)

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful and their codomain has
all pullbacks, the natural transformation `F ⟶ H` is monic iff `F` whiskered with the unit of the
adjunction `G ⊣ H` is. -/
lemma mono_leftToRight_iff_mono_whiskerLeft_unit [HasPullbacks D] :
    Mono t.leftToRight ↔ Mono (Functor.whiskerLeft F t.adj₂.unit) := by
  repeat rw [NatTrans.mono_iff_mono_app]
  exact forall_congr' fun _ ↦ t.mono_leftToRight_app_iff_mono_adj₂_unit_app

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful and their codomain has
all pullbacks, the natural transformation `F ⟶ H` is monic iff the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions is. -/
lemma mono_leftToRight_iff [HasPullbacks D] :
    Mono t.leftToRight ↔ Mono (t.adj₁.counit ≫ t.adj₂.unit) := by
  repeat rw [NatTrans.mono_iff_mono_app]
  exact t.mono_leftToRight_app_iff

end OuterFullyFaithful
