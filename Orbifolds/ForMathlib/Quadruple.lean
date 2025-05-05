import Orbifolds.ForMathlib.Triple

/-!
Lemmas on adjoint quadruples `L ⊣ F ⊣ G ⊣ R`.
TODO: upstream this to a new file `Mathlib.CategoryTheory.Adjunction.Quadruple`.
-/

open CategoryTheory Limits

-- TODO: move these somewhere else
section Misc

/-- `f : X ⟶ Y` is an epimorphism iff for all `Z`, composition of morphisms `Y ⟶ Z` with `f`
is injective. -/
lemma CategoryTheory.epi_iff_forall_injective {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} :
    Epi f ↔ ∀ Z, (fun g : Y ⟶ Z ↦ f ≫ g).Injective :=
  ⟨fun _ _ _ _ hg ↦ (cancel_epi f).1 hg, fun h ↦ ⟨fun _ _ hg ↦ h _ hg⟩⟩

/-- `f : X ⟶ Y` is a monomorphism iff for all `Z`, composition of morphisms `Z ⟶ X` with `f`
is injective. -/
lemma CategoryTheory.mono_iff_forall_injective {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} :
    Mono f ↔ ∀ Z, (fun g : Z ⟶ X ↦ g ≫ f).Injective :=
  ⟨fun _ _ _ _ hg ↦ (cancel_mono f).1 hg, fun h ↦ ⟨fun _ _ hg ↦ h _ hg⟩⟩

@[simp]
lemma CategoryTheory.op_mono_iff {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} :
    Mono f.op ↔ Epi f :=
  ⟨fun _ ↦ unop_epi_of_mono f.op, fun _ ↦ inferInstance⟩

@[simp]
lemma CategoryTheory.op_epi_iff {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} :
    Epi f.op ↔ Mono f :=
  ⟨fun _ ↦ unop_mono_of_epi f.op, fun _ ↦ inferInstance⟩

end Misc

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]
variable {L G : C ⥤ D} {F R : D ⥤ C}
variable (adj₁ : L ⊣ F) (adj₂ : F ⊣ G) (adj₃ : G ⊣ R)

section FRFullyFaithful

variable [F.Full] [F.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, all components
of the natural transformation `G ⟶ L` are epic iff all components of the natural transformation
`F ⟶ R` are monic. -/
lemma GToL_app_epi_iff_FToR_app_mono :
    (∀ X, Epi ((HToF adj₁ adj₂).app X)) ↔ ∀ X, Mono ((FToH adj₂ adj₃).app X) := by
  simp_rw [FToH_app_mono_iff_unit_app_mono, HToF_eq]
  dsimp; simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_isIso_comp_iff, epi_iff_forall_injective, mono_iff_forall_injective]
  rw [forall_comm]; refine forall_congr' fun X ↦ forall_congr' fun Y ↦ ?_
  rw [← (adj₁.homEquiv _ _).comp_injective _]
  change (fun g ↦ adj₁.homEquiv _ _ _).Injective ↔ _
  simp_rw [adj₁.homEquiv_naturality_left]
  refine ((adj₁.homEquiv _ _).injective_comp fun f ↦ _).trans ?_
  rw [← ((adj₂.homEquiv _ _).trans (adj₃.homEquiv _ _)).comp_injective _]
  change (fun g ↦ adj₃.homEquiv _ _ (adj₂.homEquiv _ _ _)).Injective ↔ _
  simp_rw [← adj₂.homEquiv_symm_id, ← adj₂.homEquiv_naturality_right_symm]
  simp_rw [← adj₃.homEquiv_id, ← adj₃.homEquiv_naturality_left]
  simp

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `G ⟶ L` is epic
iff the natural transformation `F ⟶ R` is monic. -/
lemma GToL_epi_iff_FToR_mono [HasPullbacks C] [HasPushouts D] :
    Epi (HToF adj₁ adj₂) ↔ Mono (FToH adj₂ adj₃) := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact adj₁.GToL_app_epi_iff_FToR_app_mono adj₂ adj₃

end FRFullyFaithful

section LGFullyFaithful

variable [L.Full] [L.Faithful] [G.Full] [G.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, all components
of the natural transformation `L ⟶ G` are epic iff all components of the natural transformation
`R ⟶ F` are monic. -/
lemma LToG_app_epi_iff_RToF_app_mono :
    (∀ X, Epi ((FToH adj₁ adj₂).app X)) ↔ ∀ X, Mono ((HToF adj₂ adj₃).app X) := by
  have h := GToL_app_epi_iff_FToR_app_mono adj₃.op adj₂.op adj₁.op
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simp_rw [Opposite.equivToOpposite_coe, ← HToF_app_op, ← FToH_app_op, op_mono_iff, op_epi_iff] at h
  exact h.symm

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `L ⟶ G` is epic
iff the natural transformation `R ⟶ F` is monic. -/
lemma LToG_epi_iff_RToF_mono [HasPullbacks C] [HasPushouts D] :
    Epi (FToH adj₁ adj₂) ↔ Mono (HToF adj₂ adj₃) := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact adj₁.LToG_app_epi_iff_RToF_app_mono adj₂ adj₃

end LGFullyFaithful

end CategoryTheory.Adjunction
