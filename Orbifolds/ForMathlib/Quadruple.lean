import Orbifolds.ForMathlib.Triple

/-!
Lemmas on adjoint quadruples `L ⊣ F ⊣ G ⊣ R`.
TODO: upstream this to a new file `Mathlib.CategoryTheory.Adjunction.Quadruple`.
-/

open CategoryTheory Limits Functor Adjunction Triple

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
lemma op_mono_iff {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} :
    Mono f.op ↔ Epi f :=
  ⟨fun _ ↦ unop_epi_of_mono f.op, fun _ ↦ inferInstance⟩

@[simp]
lemma op_epi_iff {C : Type*} [Category C] {X Y : C} {f : X ⟶ Y} :
    Epi f.op ↔ Mono f :=
  ⟨fun _ ↦ unop_mono_of_epi f.op, fun _ ↦ inferInstance⟩

@[simp]
lemma unop_mono_iff {C : Type*} [Category C] {X Y : Cᵒᵖ} {f : X ⟶ Y} :
    Mono f.unop ↔ Epi f :=
  ⟨fun _ ↦ op_epi_of_mono f.unop, fun _ ↦ inferInstance⟩

@[simp]
lemma unop_epi_iff {C : Type*} [Category C] {X Y : Cᵒᵖ} {f : X ⟶ Y} :
    Epi f.unop ↔ Mono f :=
  ⟨fun _ ↦ op_mono_of_epi f.unop, fun _ ↦ inferInstance⟩

end Misc

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D) (F : D ⥤ C) (G : C ⥤ D) (R : D ⥤ C)

/-- Structure containing the three adjunctions of an adjoint triple `L ⊣ F ⊣ G ⊣ R`. -/
structure CategoryTheory.Adjunction.Quadruple where
  /-- Adjunction `L ⊣ F` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ H`. -/
  adj₁ : L ⊣ F
  /-- Adjunction `F ⊣ G` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ H`. -/
  adj₂ : F ⊣ G
  /-- Adjunction `G ⊣ R` of the adjoint quadruple `L ⊣ F ⊣ G ⊣ H`. -/
  adj₃ : G ⊣ R

namespace CategoryTheory.Adjunction.Quadruple

variable {L F G R} (q : Quadruple L F G R)

/-- The left part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
def leftTriple : Triple L F G where
  adj₁ := q.adj₁
  adj₂ := q.adj₂

/-- The right part of an adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
def rightTriple : Triple F G R where
  adj₁ := q.adj₂
  adj₂ := q.adj₃

/-- The adjoint quadruple `R.op ⊣ G.op ⊣ F.op ⊣ L.op` dual to an
adjoint quadruple `L ⊣ F ⊣ G ⊣ R`. -/
@[simps]
protected def op : Quadruple R.op G.op F.op L.op where
  adj₁ := q.adj₃.op
  adj₂ := q.adj₂.op
  adj₃ := q.adj₁.op

@[simp]
lemma op_leftTriple : q.op.leftTriple = q.rightTriple.op := rfl

@[simp]
lemma op_rightTriple : q.op.rightTriple = q.leftTriple.op := rfl

section RightFullyFaithful

variable [F.Full] [F.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, all components
of the natural transformation `G ⟶ L` are epic iff all components of the natural transformation
`F ⟶ R` are monic. -/
lemma epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app :
    (∀ X, Epi (q.leftTriple.rightToLeft.app X)) ↔ ∀ X, Mono (q.rightTriple.leftToRight.app X) := by
  simp_rw [mono_leftToRight_app_iff_mono_adj₂_unit_app, rightToLeft_eq_counits]
  dsimp; simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.id_obj,
    whiskerLeft_app, Category.comp_id, Category.id_comp]
  simp_rw [epi_comp_iff_of_epi, epi_iff_forall_injective, mono_iff_forall_injective]
  rw [forall_comm]; refine forall_congr' fun X ↦ forall_congr' fun Y ↦ ?_
  rw [← (q.adj₁.homEquiv _ _).comp_injective _]
  change (fun g ↦ q.adj₁.homEquiv _ _ _).Injective ↔ _
  simp_rw [q.adj₁.homEquiv_naturality_left]
  refine ((q.adj₁.homEquiv _ _).injective_comp fun f ↦ _).trans ?_
  rw [← ((q.adj₂.homEquiv _ _).trans (q.adj₃.homEquiv _ _)).comp_injective _]
  change (fun g ↦ q.adj₃.homEquiv _ _ (q.adj₂.homEquiv _ _ _)).Injective ↔ _
  simp [← q.adj₂.homEquiv_symm_id, ← q.adj₂.homEquiv_naturality_right_symm,
    ← q.adj₃.homEquiv_id, ← q.adj₃.homEquiv_naturality_left]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `F` and `R` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `G ⟶ L` is epic
iff the natural transformation `F ⟶ R` is monic. -/
lemma epi_leftTriple_rightToLeft_iff_mono_rightTriple_leftToRight [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.rightToLeft ↔ Mono q.rightTriple.leftToRight := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app

end RightFullyFaithful

section LeftFullyFaithful

variable [L.Full] [L.Faithful] [G.Full] [G.Faithful]

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, all components
of the natural transformation `L ⟶ G` are epic iff all components of the natural transformation
`R ⟶ F` are monic. -/
lemma epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app :
    (∀ X, Epi (q.leftTriple.leftToRight.app X)) ↔ ∀ X, Mono (q.rightTriple.rightToLeft.app X) := by
  have h := q.op.epi_leftTriple_rightToLeft_app_iff_mono_rightTriple_leftToRight_app
  rw [← (Opposite.equivToOpposite (α := C)).forall_congr_right] at h
  rw [← (Opposite.equivToOpposite (α := D)).forall_congr_right] at h
  simpa using h.symm

/-- For an adjoint quadruple `L ⊣ F ⊣ G ⊣ R` where `L` and `G` are fully faithful, their domain
has all pushouts and their codomain has all pullbacks, the natural transformation `L ⟶ G` is epic
iff the natural transformation `R ⟶ F` is monic. -/
lemma epi_leftTriple_leftToRight_iff_mono_rightTriple_rightToLeft [HasPullbacks C] [HasPushouts D] :
    Epi q.leftTriple.leftToRight ↔ Mono q.rightTriple.rightToLeft := by
  rw [NatTrans.epi_iff_epi_app, NatTrans.mono_iff_mono_app]
  exact q.epi_leftTriple_leftToRight_app_iff_mono_rightTriple_rightToLeft_app

end LeftFullyFaithful

end CategoryTheory.Adjunction.Quadruple
