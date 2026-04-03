import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Subobject classifiers in categories of sheaves
In this file we construct a subobject classifier in the category of sheaves of types on any site, as
the sheaf that sends every object to the set of closed sieves on it.
See https://ncatlab.org/nlab/show/subobject+classifier#in_a_sheaf_topos.

For Grothendieck topologies `J ≤ K` we also construct comparison maps between the corresponding
subobject classifiers, both viewed as `J`-sheaves.

## Main definitions / results
* `ClosedSieve J X`: the type of `J`-closed sieves on `X`
* `J.Ω`: the `J`-sheaf sending each `X` to the type of `J`-closed sieves on `X`
* `J.classifier`: the data making `J.Ω` into a subobject classifier
* `J.Ω' h`: `K.Ω` as a `J`-sheaf for `h : J ≤ K`
* `J.ΩInclusionOfLE h`: the inclusion `J.Ω' h ⟶ J.Ω` for `h : J ≤ K`
* `J.ΩProjectionOfLE h`: the projection `J.Ω ⟶ J.Ω' h` for `h : J ≤ K`
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

variable {J} in
lemma Sieve.IsClosed.anti {K : GrothendieckTopology C} (h : J ≤ K) {X : C} {S : Sieve X}
    (hS : S.IsClosed K) : S.IsClosed J :=
  fun Y f hf ↦ hS Y f <| h _ hf

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

@[simps! toSieve]
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

/-- The inclusion of `K`-closed sieves into `J`-closed sieves for `J ≤ K`. -/
@[simps! toSieve]
def inclusionOfLE {K : GrothendieckTopology C} (h : J ≤ K) {X : C} (S : ClosedSieve K X) :
    ClosedSieve J X :=
  ⟨_, S.isClosed.anti h⟩

/-- The `K`-closed sieve generated by the sieve underlying a `J`-closed sieve. For `J ≤ K`, this
is left adjoint to `inclusionOfLE : ClosedSieve K X → ClosedSieve J X`. -/
@[simps!]
def toClosedSieve (K : GrothendieckTopology C) {X : C} (S : ClosedSieve J X) :
    ClosedSieve K X :=
  generate K (S.toSieve)

lemma toClosedSieve_le_iff_le_inclusionOfLE {K : GrothendieckTopology C} (h : J ≤ K) {X : C}
    (S : ClosedSieve J X) (T : ClosedSieve K X) :
    S.toClosedSieve K ≤ T ↔ S ≤ T.inclusionOfLE h :=
  generate_le_iff _ _

lemma le_inclusionOfLE_toClosedSieve {K : GrothendieckTopology C} (h : J ≤ K) {X : C}
    (S : ClosedSieve J X) : S ≤ (S.toClosedSieve K).inclusionOfLE h :=
  (toClosedSieve_le_iff_le_inclusionOfLE h _ _).1 le_rfl

/-- The galois insertion given by `inclusionOfLE h : ClosedSieve K X → ClosedSieve J X`. -/
def giInclusionOfLE {K : GrothendieckTopology C} (h : J ≤ K) {X : C} :
    GaloisInsertion (toClosedSieve K (X := X)) (inclusionOfLE h) where
  gc := toClosedSieve_le_iff_le_inclusionOfLE h
  le_l_u S := (generate_toSieve _).symm.le
  choice S hS := ⟨S.toSieve, le_antisymm hS (le_inclusionOfLE_toClosedSieve h _) ▸ isClosed _⟩
  choice_eq S hS := by ext1; exact le_antisymm (le_inclusionOfLE_toClosedSieve h _) hS

@[simp]
lemma toClosedSieve_inclusionOfLE {K : GrothendieckTopology C} (h : J ≤ K) {X : C}
    (S : ClosedSieve K X) : (S.inclusionOfLE h).toClosedSieve K = S :=
  (giInclusionOfLE h).l_u_eq S

end ClosedSieve

/-- A specific choice of subobject classifier in the sheaf topos `Sheaf J (Type max u v)`: the
sheaf that associates to each `X : C` the type of all `J`-closed sieves on `X`. The data that
makes this a subobject classifier can be found in `GrothendieckTopology.classifier`. -/
@[simps! obj_obj obj_map]
protected def GrothendieckTopology.Ω : Sheaf J (Type max u v) where
  obj := {
    obj X := ClosedSieve J X.unop
    map f S := S.pullback f.unop
    map_id _ := by ext S; simp
    map_comp _ _ := by ext S; rw [unop_comp, S.pullback_comp]; rfl
  }
  property := by
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
lemma Subfunctor.isSheaf_range {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F F' : Sheaf J (Type w)} (f : F ⟶ F') [Mono f] :
    Presieve.IsSheaf J (Subfunctor.range f.hom).toFunctor := by
  have : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  exact Presieve.isSheaf_iso J (asIso (Subfunctor.toRange f.hom)) <|
    (isSheaf_iff_isSheaf_of_type J _).1 <| F.2

-- TODO: move to `Mathlib.CategoryTheory.Subfunctor.Sieves`
lemma Subfunctor.sieveOfSection_eq_top_iff {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {G : Subfunctor F} {U : Cᵒᵖ} {s : F.obj U} :
    G.sieveOfSection s = ⊤ ↔ s ∈ G.obj U := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [← Sieve.id_mem_iff_eq_top] using h
  · ext _ f; simpa using G.map f.op h

-- TODO: move to `Mathlib.CategoryTheory.Subfunctor.Sieves`
lemma Subfunctor.pullback_sieveOfSection {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {G : Subfunctor F} {U V : Cᵒᵖ} (f : U ⟶ V) (s : F.obj U) :
    (G.sieveOfSection s).pullback f.unop = G.sieveOfSection (F.map f s) := by
  ext; simp

lemma Subfunctor.isClosed_sieveOfSection {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ Type w} (hF : Presieve.IsSheaf J F) {G : Subfunctor F}
    (hG : Presieve.IsSheaf J G.toFunctor) {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).IsClosed J :=
  fun _ f hf ↦ (Subfunctor.isSheaf_iff _ hF).1 hG _ _ <|
    J.superset_covering (G.pullback_sieveOfSection f.op s).le hf

/- A few lemmas for which I haven't found a better place yet.
TODO: clean up. -/
section TerminalSheaf

/-- Evaluating a terminal functor yields terminal objects.
TODO: move somewhere else -/
noncomputable def Limits.IsTerminal.isTerminalObj_functor {C : Type u} [Category.{v} C]
    {D : Type u₂} [Category.{v₂} D] [HasLimits D] {F : C ⥤ D} (hF : IsTerminal F) (X : C) :
    IsTerminal (F.obj X) :=
  hF.isTerminalObj ((evaluation C D).obj X)

/-- A terminal sheaf is also terminal as a presheaf. -/
noncomputable def Limits.IsTerminal.isTerminalSheafVal {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    {X : Sheaf J A} (hX : IsTerminal X) : IsTerminal X.obj :=
  hX.isTerminalObj (sheafToPresheaf J A)

/-- Sections of a terminal sheaf are terminal objects. -/
noncomputable def Limits.IsTerminal.isTerminalSheafValObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    {X : Sheaf J A} (hX : IsTerminal X) (Y : Cᵒᵖ) : IsTerminal (X.obj.obj Y) :=
  hX.isTerminalSheafVal.isTerminalObj_functor Y

/-- For sheaves valued in a concrete category whose terminal object is a point,
sections of the terminal sheaf are unique. -/
noncomputable instance Sheaf.instUniqueTerminalValObjForget {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {A : Type u₂} [Category.{v₂} A] [HasLimits A]
    {FA : outParam (A → A → Type w)} {CA : outParam (A → Type w)}
    [outParam ((X Y : A) → FunLike (FA X Y) (CA X) (CA Y))] [ConcreteCategory A FA]
    [PreservesLimit (Functor.empty _) (forget A)] (Y : Cᵒᵖ) :
    Unique (CA ((⊤_ Sheaf J A).obj.obj Y)) :=
  (Types.isTerminalEquivUnique _).1 <|
    (terminalIsTerminal.isTerminalSheafValObj Y).isTerminalObj (forget _) _

/-- Terminal types are singletons. -/
@[implicit_reducible]
noncomputable def Limits.IsTerminal.unique {X : Type u} (h : IsTerminal X) : Unique X :=
  Types.isTerminalEquivUnique _ h

/-- Sections of the terminal sheaf are unique. -/
noncomputable instance Sheaf.instUniqueTerminalValObj {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}  (Y : Cᵒᵖ) :
    Unique ((⊤_ Sheaf J (Type w)).obj.obj Y) :=
  (terminalIsTerminal.isTerminalSheafValObj Y).unique

end TerminalSheaf

namespace GrothendieckTopology

set_option backward.isDefEq.respectTransparency false in
/-- A specific choice of subobject classifier in the sheaf topos `Sheaf J (Type max u v)`, given
by `J.Ω` and the morphism `⊤_ C ⟶ J.Ω` that picks the maximal sieve on each object. -/
noncomputable def classifier : Classifier (Sheaf J (Type max u v)) :=
  .mkOfTerminalΩ₀ _ terminalIsTerminal J.Ω
    ⟨{ app _ := fun _ ↦ (⊤ : ClosedSieve J _) }⟩
    (fun {F G} i _ ↦ ⟨{
      app X x := ⟨(Subfunctor.range i.hom).sieveOfSection x, Subfunctor.isClosed_sieveOfSection
        ((isSheaf_iff_isSheaf_of_type J _).1 <| G.2) ((Subfunctor.isSheaf_range i)) x⟩ }⟩)
    (fun {F G} i _ ↦ by
      refine ⟨⟨by ext X x; dsimp; ext1; exact Subfunctor.sieveOfSection_eq_top_iff.2 (by simp)⟩,
        ⟨isLimitOfReflects (sheafToPresheaf J (Type max u v)) ?_⟩⟩
      refine evaluationJointlyReflectsLimits _ fun X ↦ ?_
      refine Nonempty.some <| (Types.isLimit_iff _).2 fun s hs ↦ ?_
      have hs' := Subfunctor.sieveOfSection_eq_top_iff.1 <| congrArg ClosedSieve.toSieve <|
        (hs WalkingCospan.Hom.inl).trans (hs WalkingCospan.Hom.inr).symm
      let ⟨x, hx, hx'⟩ := Function.Injective.existsUnique_of_mem_range
        (by have : Mono i.hom := (sheafToPresheaf J _).map_mono i; exact injective_of_mono _) hs'
      refine ⟨x, ?_, fun y hy ↦ hx' y (hy WalkingCospan.left)⟩
      exact Option.rec (by dsimp; exact hx ▸ hs WalkingCospan.Hom.inl) <| WalkingPair.rec hx <|
        @Subsingleton.elim _ (by dsimp; infer_instance) _ _)
    (fun {F G} i _ χ hχ ↦ by
      ext X x; dsimp; ext Y f
      replace hχ := hχ.map (sheafToPresheaf J _ ⋙ (evaluation _ _).obj (op Y))
      dsimp at hχ
      replace hχ : χ.hom.app (op Y) (G.obj.map f.op x) = (⊤ : ClosedSieve _ _) ↔
          G.obj.map f.op x ∈ Set.range (i.hom.app (op Y)) := by
        refine ⟨fun hy ↦ ?_, fun hy ↦ by simpa [hy.choose_spec] using congrFun hχ.w hy.choose⟩
        exact ⟨_, PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst hχ.isLimit
          ⟨((G.obj.map f.op x), default), hy⟩⟩
      refine ((Sieve.mem_iff_pullback_eq_top _).trans ?_).trans hχ
      rw [show χ.hom.app _ _ = _ from congrFun (χ.hom.naturality f.op) x, ClosedSieve.ext_iff]; rfl)

instance hasClassifier : HasClassifier (Sheaf J (Type max u v)) :=
  ⟨⟨J.classifier⟩⟩

-- TODO: move to `Mathlib.CategoryTheory.Sites.Sheaf`
lemma _root_.CategoryTheory.Presheaf.isSheaf_of_le {C : Type u} [Category.{v} C] {A : Type u₂}
    [Category.{v₂} A] {P : Cᵒᵖ ⥤ A} {J K : GrothendieckTopology C} (h : J ≤ K)
    (hP : Presheaf.IsSheaf K P) : Presheaf.IsSheaf J P :=
  fun X ↦ Presieve.isSheaf_of_le _ h <| hP X

variable {J} {K : GrothendieckTopology C} (h : J ≤ K)

/-- The subobject classifier sheaf `K.Ω : Sheaf K (Type max u v)` as a `J`-sheaf for `J ≤ K`. -/
@[simps!]
protected def Ω' : Sheaf J (Type max u v) :=
  ⟨K.Ω.obj, Presheaf.isSheaf_of_le h K.Ω.2⟩

/-- The inclusion of `J.Ω' h`, the subobject classifier of `K`-sheaves viewed as a `J`-sheaf,
into `J.Ω`, the subobject classifier of `J`-sheaves. In components this is simply the inclusion of
`K`-closed sieves into `J`-closed sieves. -/
@[simps! hom_app]
def ΩInclusionOfLE : J.Ω' h ⟶ J.Ω :=
  ⟨{ app X := ClosedSieve.inclusionOfLE h (X := unop X) }⟩

/-- The projection of `J.Ω`, the subobject classifier of `J`-sheaves, onto `J.Ω' h`, the subobject
classifier of `K`-sheaves viewed as a `J`-sheaf. In components this generates `K`-closed sieves from
`J`-closed sieves. -/
@[simps! hom_app]
def ΩProjectionOfLE : J.Ω ⟶ J.Ω' h :=
  ⟨{
    app X := ClosedSieve.toClosedSieve K (X := unop X)
    naturality X Y f := by dsimp; ext; simp [Sieve.pullback_comp]
  }⟩

@[simp]
lemma ΩInclusionOfLE_comp_ΩProjectionOfLE :
    ΩInclusionOfLE h ≫ ΩProjectionOfLE h = 𝟙 (J.Ω' h) := by
  ext; simp

instance : Mono (ΩInclusionOfLE h) := mono_of_mono_fac (ΩInclusionOfLE_comp_ΩProjectionOfLE h)

instance : Epi (ΩProjectionOfLE h) := epi_of_epi_fac (ΩInclusionOfLE_comp_ΩProjectionOfLE h)

end GrothendieckTopology

end CategoryTheory
