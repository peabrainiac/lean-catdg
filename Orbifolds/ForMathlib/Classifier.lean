import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Subobject classifiers in categories of sheaves
A construction of subobject classifiers in the category of sheaves on any site.
-/

universe u v w u₂ v₂

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A sieve is called `J`-closed if it contains every morphism along which it pulls back to a
`J`-covering sieve, i.e. if it contains every morphism it covers. -/
def Sieve.IsClosed {X : C} (S : Sieve X) : Prop :=
  ∀ Y (f : Y ⟶ X), S.pullback f ∈ J Y → S f

variable {J} in
lemma Sieve.IsClosed.pullback {X : C} {S : Sieve X} (hS : S.IsClosed J) {Y : C} (f : Y ⟶ X) :
    (S.pullback f).IsClosed J :=
  fun _ _ h ↦ hS _ _ <| S.pullback_comp ▸ h

/-- A sieve on `X` that is `J`-closed in the sense of `Sieve.IsClosed`, i.e. that contains every
morphism along which it pulls back to a `J`-covering sieve. -/
structure ClosedSieve (X : C) extends Sieve X where
  isClosed : toSieve.IsClosed J

initialize_simps_projections ClosedSieve (arrows → apply)

namespace ClosedSieve

variable {J}

@[ext]
protected lemma ext {X : C} (S T : ClosedSieve J X) :
    S.toSieve = T.toSieve → S = T :=
  S.rec fun S hS ↦ T.rec fun T hT h ↦ by simpa using h

lemma injective_toSieve {X : C} : (toSieve : ClosedSieve J X → Sieve X).Injective := by
  intro S T h; ext1; exact h

instance {X : C} : PartialOrder (ClosedSieve J X) :=
  PartialOrder.lift _ ClosedSieve.injective_toSieve

protected lemma le_def {X : C} {S T : ClosedSieve J X} : S ≤ T ↔ S.toSieve ≤ T.toSieve := Iff.rfl

variable (J) in
/-- The smallest `J`-closed sieve containing a given sieve `S : Sieve X`, given by all morphisms
`f : Y ⟶ X` along which `S` pulls back to a covering sieve, i.e. "all morphisms that `S` covers". -/
@[simps!]
def generate {X : C} (S : Sieve X) : ClosedSieve J X where
  arrows Y f := S.pullback f ∈ J Y
  downward_closed hf g := S.pullback_comp ▸ J.pullback_stable g hf
  isClosed _ _ hf := J.transitive hf _ fun _ _ hg ↦ S.pullback_comp ▸ hg

lemma generate_le_iff {X : C} (S : Sieve X) (T : ClosedSieve J X) :
    ClosedSieve.generate J S ≤ T ↔ S ≤ T.toSieve :=
  ⟨fun h _ _ hf ↦ h _ <| J.covering_of_eq_top <| S.pullback_eq_top_of_mem hf,
    fun h _ _ hf ↦ T.isClosed _ _ <| J.superset_covering (Sieve.pullback_monotone _ h) hf⟩

lemma le_toSieve_generate {X : C} (S : Sieve X) : S ≤ (generate J S).toSieve :=
  (generate_le_iff _ _).1 le_rfl

/-- The Galois insertion given by `ClosedSieve.generate : Sieve X → ClosedSieve J X`. -/
def giGenerate {X : C} : GaloisInsertion (generate J (X := X)) toSieve where
  gc := generate_le_iff
  le_l_u S _ _ hf := J.covering_of_eq_top <| S.pullback_eq_top_of_mem hf
  choice S hS := ⟨S, le_antisymm hS (le_toSieve_generate _) ▸ (generate J S).isClosed⟩
  choice_eq S hS := by ext1; exact le_antisymm (le_toSieve_generate _) hS

@[simp]
lemma generate_toSieve {X : C} (S : ClosedSieve J X) : generate J S.toSieve = S :=
  giGenerate.l_u_eq S

instance {X : C} : CompleteLattice (ClosedSieve J X) := giGenerate.liftCompleteLattice

@[simps!]
def pullback {X Y : C} (f : Y ⟶ X) (S : ClosedSieve J X) : ClosedSieve J Y :=
  ⟨_, S.isClosed.pullback f⟩

@[simp]
lemma pullback_id {X : C} (S : ClosedSieve J X) : S.pullback (𝟙 X) = S := by
  ext; simp

lemma pullback_comp {X : C} (S : ClosedSieve J X) {Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} :
    S.pullback (g ≫ f) = (S.pullback f).pullback g := by
  ext; simp

lemma pullback_monotone {X Y : C} {f : Y ⟶ X} : Monotone (pullback (J := J) f) :=
  fun _ _ h ↦ Sieve.pullback_monotone f h

lemma pullback_generate {X : C} (S : Sieve X) {Y : C} (f : Y ⟶ X) :
    pullback f (generate J S) = generate J (S.pullback f) := by
  ext Z g; simp [Sieve.pullback_comp]

end ClosedSieve

/-- A specific choice of subobject classifier in the sheaf topos `Sheaf J (Type max u v)`: the
sheaf that associates to each `X : C` the type of all `J`-closed sieves on `X`. The data that
makes this a subobject classifier can be found in `GrothendieckTopology.classifier`. -/
@[simps!]
protected def GrothendieckTopology.Ω : Sheaf J (Type max u v) where
  val := {
    obj X := ClosedSieve J X.unop
    map f S := S.pullback f.unop
    map_id _ := by ext S; simp
    map_comp _ _ := by ext S; rw [unop_comp, S.pullback_comp]; rfl
  }
  cond := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro X S hS T hT
    refine ⟨ClosedSieve.generate J <| .bind S fun Y f hf ↦ (T f hf).toSieve, ?_, ?_⟩
    · refine fun Y f hf ↦ le_antisymm ?_ ?_
      · dsimp; rw [ClosedSieve.pullback_generate, ClosedSieve.generate_le_iff]
        intro Z g ⟨W, g', f', hf', hg', h⟩
        dsimp only at hg'
        rw [Sieve.mem_iff_pullback_eq_top] at hg' ⊢
        exact (congrArg ClosedSieve.toSieve (hT _ _ hf' hf h)).symm.trans hg'
      · refine ClosedSieve.le_def.2 ?_
        refine le_trans ?_ <| Sieve.pullback_monotone f <| ClosedSieve.le_toSieve_generate _
        exact Sieve.le_pullback_bind _ (fun Y f hf ↦ (T f hf).toSieve) _ hf
    · refine fun R hR ↦ le_antisymm ?_ ?_
      · refine fun Y f hf ↦ J.transitive (J.pullback_stable f hS) _ fun Z g hg ↦ ?_
        rw [← Sieve.pullback_comp]
        refine J.superset_covering
          (Sieve.le_pullback_bind _ (fun Y f hf ↦ (T f hf).toSieve) _ hg) ?_
        rw [← hR _ hg]
        exact J.covering_of_eq_top <| Sieve.pullback_eq_top_of_mem _ <| R.downward_closed hf g
      · rw [R.generate_le_iff]
        intro Y f ⟨Z, g, g', hg', hg, h⟩
        dsimp only at hg
        exact h ▸ (hR g' hg' ▸ hg:)

-- TODO: move to `Mathlib.CategoryTheory.Sites.Subsheaf`
lemma Subpresheaf.isSheaf_range {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F F' : Sheaf J (Type w)} (f : F ⟶ F') [Mono f] :
    Presieve.IsSheaf J (Subpresheaf.range f.val).toPresheaf := by
  have : Mono f.val := (sheafToPresheaf _ _).map_mono f
  exact Presieve.isSheaf_iso J (asIso (Subpresheaf.toRange f.val)) <|
    (isSheaf_iff_isSheaf_of_type J _).1 <| F.2

-- TODO: move to `Mathlib.CategoryTheory.Subpresheaf.Sieves`
lemma Subpresheaf.sieveOfSection_eq_top_iff {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {G : Subpresheaf F} {U : Cᵒᵖ} {s : F.obj U} :
    G.sieveOfSection s = ⊤ ↔ s ∈ G.obj U := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [← Sieve.id_mem_iff_eq_top] using h
  · ext _ f; simpa using G.map f.op h

-- TODO: move to `Mathlib.CategoryTheory.Subpresheaf.Sieves`
lemma Subpresheaf.pullback_sieveOfSection {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {G : Subpresheaf F} {U V : Cᵒᵖ} (f : U ⟶ V) (s : F.obj U) :
    (G.sieveOfSection s).pullback f.unop = G.sieveOfSection (F.map f s) := by
  ext; simp

lemma Subpresheaf.isClosed_sieveOfSection {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type w} (hF : Presieve.IsSheaf J F) {G : Subpresheaf F}
    (hG : Presieve.IsSheaf J G.toPresheaf) {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).IsClosed J :=
  fun _ f hf ↦ (Subpresheaf.isSheaf_iff _ hF).1 hG _ _ <|
    J.superset_covering (G.pullback_sieveOfSection f.op s).le hf

/- A few lemmas for which I haven't found a better place yet.
TODO: clean up. -/
section TerminalSheaf

attribute [local instance] HasForget.hasCoeToSort
attribute [local instance] HasForget.instFunLike

/-- Evaluating a terminal functor yields terminal objects.
TODO: move somewhere else -/
noncomputable def Limits.IsTerminal.isTerminalObj_functor {C : Type u} [Category.{v} C]
    {D : Type u₂} [Category.{v₂} D] [HasLimits D] {F : C ⥤ D} (hF : IsTerminal F) (X : C) :
    IsTerminal (F.obj X) :=
  hF.isTerminalObj ((evaluation C D).obj X)

/-- A terminal sheaf is also terminal as a presheaf. -/
noncomputable def Limits.IsTerminal.isTerminalSheafVal {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    {X : Sheaf J A} (hX : IsTerminal X) : IsTerminal X.val :=
  hX.isTerminalObj (sheafToPresheaf J A)

/-- Sections of a terminal sheaf are terminal objects. -/
noncomputable def Limits.IsTerminal.isTerminalSheafValObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    {X : Sheaf J A} (hX : IsTerminal X) (Y : Cᵒᵖ) : IsTerminal (X.val.obj Y) :=
  hX.isTerminalSheafVal.isTerminalObj_functor Y

/-- For sheaves valued in a concrete category whose terminal object is a point,
sections of the terminal sheaf are unique. -/
noncomputable instance Sheaf.instUniqueTerminalValObjForget {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    [HasForget.{w} A] [PreservesLimit (Functor.empty _) (forget A)] (Y : Cᵒᵖ) :
    Unique ((⊤_ Sheaf J A).val.obj Y) :=
  (Types.isTerminalEquivUnique _).1 <|
    (terminalIsTerminal.isTerminalSheafValObj Y).isTerminalObj (forget _) _

/-- Terminal types are singletons. -/
noncomputable def Limits.IsTerminal.unique {X : Type u} (h : IsTerminal X) : Unique X :=
  Types.isTerminalEquivUnique _ h

/-- Sections of the terminal sheaf are unique. -/
noncomputable instance Sheaf.instUniqueTerminalValObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}  (Y : Cᵒᵖ) :
    Unique ((⊤_ Sheaf J (Type w)).val.obj Y) :=
  (terminalIsTerminal.isTerminalSheafValObj Y).unique

end TerminalSheaf

/-- A specific choice of subobject classifier in the sheaf topos `Sheaf J (Type max u v)`, given
by `J.Ω` and the morphism `⊤_ C ⟶ J.Ω` that picks the maximal sieve on each object. -/
noncomputable def GrothendieckTopology.classifier : Classifier (Sheaf J (Type max u v)) :=
  .mkOfTerminalΩ₀ _ terminalIsTerminal J.Ω
    ⟨{ app _ := fun _ ↦ (⊤ : ClosedSieve J _) }⟩
    (fun {F G} i _ ↦ ⟨{
      app X x := ⟨(Subpresheaf.range i.val).sieveOfSection x, Subpresheaf.isClosed_sieveOfSection
        ((isSheaf_iff_isSheaf_of_type J _).1 <| G.2) ((Subpresheaf.isSheaf_range i)) x⟩ }⟩)
    (fun {F G} i _ ↦ by
      refine ⟨⟨by ext X x; dsimp; ext1; exact Subpresheaf.sieveOfSection_eq_top_iff.2 (by simp)⟩,
        ⟨isLimitOfReflects (sheafToPresheaf J (Type max u v)) ?_⟩⟩
      refine evaluationJointlyReflectsLimits _ fun X ↦ ?_
      refine Nonempty.some <| (Types.isLimit_iff _).2 fun s hs ↦ ?_
      have hs' := Subpresheaf.sieveOfSection_eq_top_iff.1 <| congrArg ClosedSieve.toSieve <|
        (hs WalkingCospan.Hom.inl).trans (hs WalkingCospan.Hom.inr).symm
      let ⟨x, hx, hx'⟩ := Function.Injective.existsUnique_of_mem_range
        (by have : Mono i.val := (sheafToPresheaf J _).map_mono i; exact injective_of_mono _) hs'
      refine ⟨x, ?_, fun y hy ↦ hx' y (hy WalkingCospan.left)⟩
      exact Option.rec (by dsimp; exact hx ▸ hs WalkingCospan.Hom.inl) <| WalkingPair.rec hx <|
        @Subsingleton.elim _ (by dsimp; infer_instance) _ _)
    (fun {F G} i _ χ hχ ↦ by
      ext X x; dsimp; ext Y f
      replace hχ := hχ.map (sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op Y))
      dsimp at hχ
      replace hχ : χ.val.app (op Y) (G.val.map f.op x) = (⊤ : ClosedSieve _ _) ↔
          G.val.map f.op x ∈ Set.range (i.val.app (op Y)) := by
        refine ⟨fun hy ↦ ?_, fun hy ↦ by simpa [hy.choose_spec] using congrFun hχ.w hy.choose⟩
        exact ⟨_, PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst hχ.isLimit
          ⟨((G.val.map f.op x), default), hy⟩⟩
      refine ((Sieve.mem_iff_pullback_eq_top _).trans ?_).trans hχ
      rw [show χ.val.app _ _ = _ from congrFun (χ.val.naturality f.op) x, ClosedSieve.ext_iff]; rfl)

instance GrothendieckTopology.hasClassifier : HasClassifier (Sheaf J (Type max u v)) :=
  ⟨⟨J.classifier⟩⟩

end CategoryTheory
