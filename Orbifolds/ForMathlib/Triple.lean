import Mathlib.CategoryTheory.Adjunction.Triple

/-!
Lemmas that should go into `Mathlib.CategoryTheory.Adjunction.Triple`.
-/

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]
variable {F H : C ⥤ D} {G : D ⥤ C}
variable (adj₁ : F ⊣ G) (adj₂ : G ⊣ H)

section InnerFullyFaithful

variable [G.Full] [G.Faithful]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the two natural transformations
`H ⋙ G ⋙ F ⟶ F ⋙ G ⋙ H` obtained by following the whiskered counit and units of either
adjunction agree. Note that this is also true when `F` and `H` are fully faithful instead of `G`;
see `whiskered_counit_unit_eq_of_outer` for the corresponding variant of this lemma. -/
lemma whiskered_counit_unit_eq_of_inner :
    whiskerLeft H adj₁.counit ≫ H.rightUnitor.hom ≫ H.leftUnitor.inv ≫
    whiskerRight adj₁.unit H ≫ (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F ≫ F.leftUnitor.hom ≫
    F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit := by
  ext X
  dsimp; simp only [Category.id_comp, Category.comp_id]
  refine (adj₁.counit_naturality <| (whiskerRight adj₁.unit H).app X).symm.trans ?_
  rw [whiskerRight_app, (asIso (adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (adj₂.counit_naturality (adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| adj₂.left_triangle_components (F.obj X)]
  simp

/-- The natural transformation `H ⟶ F` that exists for every adjoint triple `F ⊣ G ⊣ H` where `G`
is fully faithful, given here as the whiskered unit `H ⟶ F ⋙ G ⋙ H` of the first adjunction
followed by the inverse of the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second. -/
@[simps!]
noncomputable def HToF : H ⟶ F :=
  H.leftUnitor.inv ≫ whiskerRight adj₁.unit H ≫ (Functor.associator _ _ _).hom ≫
  inv (whiskerLeft F adj₂.unit) ≫ F.rightUnitor.hom

/-- The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fully faithful
is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first adjunction
followed by the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second. -/
lemma HToF_eq :
    HToF adj₁ adj₂ = H.rightUnitor.inv ≫ inv (whiskerLeft H adj₁.counit) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F ≫ F.leftUnitor.hom := by
  ext X; dsimp [HToF]
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Category.comp_id, Category.id_comp]
  rw [IsIso.comp_inv_eq]
  simpa using congr_app (whiskered_counit_unit_eq_of_inner adj₁ adj₂) X

omit [G.Full] [G.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the unit of the first adjunction under `H`. -/
lemma homEquiv_counit_unit_app_eq_H_map_unit {X : C} :
    adj₂.homEquiv _ _ (adj₂.counit.app X ≫ adj₁.unit.app X) = H.map (adj₁.unit.app X) := by
  simp [Adjunction.homEquiv_apply]

omit [G.Full] [G.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the counit of the second adjunction under `F`. -/
lemma homEquiv_symm_counit_unit_app_eq_F_map_counit {X : C} :
    (adj₁.homEquiv _ _).symm (adj₂.counit.app X ≫ adj₁.unit.app X) = F.map (adj₂.counit.app X) := by
  simp [Adjunction.homEquiv_symm_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the components of the natural
transformation `H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are simply
the images of the components of the natural transformation `H ⟶ F` under `G`. -/
lemma counit_unit_app_eq_map_HToF {X : C} :
    adj₂.counit.app X ≫ adj₁.unit.app X = G.map ((HToF adj₁ adj₂).app X) := by
  refine ((adj₂.homEquiv _ _).symm_apply_apply _).symm.trans ?_
  rw [homEquiv_counit_unit_app_eq_H_map_unit]; dsimp
  rw [Adjunction.homEquiv_symm_apply, ← Adjunction.inv_map_unit, ← G.map_inv,
    ← G.map_comp, HToF_app]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions is simply the
natural transformation `H ⟶ F` whiskered with `G`. -/
lemma counit_unit_eq_whiskerRight : adj₂.counit ≫ adj₁.unit = whiskerRight (HToF adj₁ adj₂) G := by
  ext X; exact counit_unit_app_eq_map_HToF adj₁ adj₂

end InnerFullyFaithful

section OuterFullyFaithful

variable [F.Full] [F.Faithful] [H.Full] [H.Faithful]

omit [F.Full] [F.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the two natural
transformations `H ⋙ G ⋙ F ⟶ F ⋙ G ⋙ H` obtained by following the whiskered counit and unit
of either adjunction agree. Note that this is also true when `G` is fully faithful instead of `F`
and `H`; see `whiskered_counit_unit_eq_of_inner` for the corresponding variant of this lemma.-/
lemma whiskered_counit_unit_eq_of_outer :
    whiskerLeft H adj₁.counit ≫ H.rightUnitor.hom ≫ H.leftUnitor.inv ≫
    whiskerRight adj₁.unit H ≫ (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F ≫ F.leftUnitor.hom ≫
    F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit := by
  ext X
  dsimp; simp only [Category.id_comp, Category.comp_id]
  refine (adj₁.counit_naturality <| (whiskerRight adj₁.unit H).app X).symm.trans ?_
  rw [whiskerRight_app, (asIso (adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (adj₂.counit_naturality (adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| adj₂.left_triangle_components (F.obj X)]
  simp

/-- The natural transformation `F ⟶ H` that exists for every adjoint triple `F ⊣ G ⊣ H` where `F`
and `H` are fully faithful, given here as the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second
adjunction followed by the inverse of the whiskered unit `F ⋙ G ⋙ H ⟶ H` of the first. -/
@[simps!]
noncomputable def FToH : F ⟶ H :=
  F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight adj₁.unit H) ≫ H.leftUnitor.hom

/-- The natural transformation `F ⟶ H` for an adjoint triple `F ⊣ G ⊣ H` with `F` and `H`
fully faithful is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second
adjunction followed by the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first. -/
lemma FToH_eq :
    FToH adj₁ adj₂ = F.leftUnitor.inv ≫ inv (whiskerRight adj₂.counit F) ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft H adj₁.counit ≫ H.rightUnitor.hom := by
  ext X; dsimp [FToH]
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Category.comp_id, Category.id_comp]
  rw [IsIso.comp_inv_eq]
  simpa using congr_app (whiskered_counit_unit_eq_of_outer adj₁ adj₂).symm X

omit [F.Full] [F.Faithful] [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the unit of the second adjunction under `G`. -/
lemma homEquiv_counit_unit_app_eq_G_map_unit {X : D} :
    adj₁.homEquiv _ _ (adj₁.counit.app X ≫ adj₂.unit.app X) = G.map (adj₂.unit.app X) := by
  simp [homEquiv_apply]

omit [F.Full] [F.Faithful] [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the counit of the first adjunction under `G`. -/
lemma homEquiv_symm_counit_unit_app_eq_G_map_counit {X : D} :
    (adj₂.homEquiv _ _).symm (adj₁.counit.app X ≫ adj₂.unit.app X) = G.map (adj₁.counit.app X) := by
  simp [homEquiv_symm_apply]

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions
are simply the components of the natural transformation `F ⟶ H` at `G`. -/
lemma counit_unit_app_eq_FToH_app {X : D} :
    adj₁.counit.app X ≫ adj₂.unit.app X = (FToH adj₁ adj₂).app (G.obj X) := by
  refine ((adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_
  rw [homEquiv_symm_counit_unit_app_eq_G_map_counit, adj₂.homEquiv_apply, FToH_app, ← H.map_inv]
  congr
  exact IsIso.eq_inv_of_hom_inv_id (adj₁.right_triangle_components _)

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions is simply
the natural transformation `F ⟶ H` whiskered from the left with `G`. -/
lemma counit_unit_eq_whiskerLeft : adj₁.counit ≫ adj₂.unit = whiskerLeft G (FToH adj₁ adj₂) := by
  ext X; exact counit_unit_app_eq_FToH_app adj₁ adj₂

end OuterFullyFaithful
