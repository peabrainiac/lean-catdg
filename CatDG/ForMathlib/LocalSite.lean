import CatDG.ForMathlib.CoconstantSheaf
import CatDG.ForMathlib.MorphismProperty

/-!
# Local sites
A site (C,J) is called local if it has a terminal object whose only covering sieve is trivial -
this makes it possible to define coconstant sheaves on it, giving its sheaf topos the structure
of a local topos. This makes them an important stepping stone to cohesive sites.

See https://ncatlab.org/nlab/show/local+site.

## Main definitions / results
* `J.IsLocalSite`: typeclass stating that (C,J) is a local site.
* `coconstantSheaf`: the coconstant sheaf functor `Type w ⥤ Sheaf J (Type max v w)` defined on any
  local site.
* `ΓCoconstantSheafAdj`: the adjunction between the global sections functor `Γ` and
  `coconstantSheaf`.
* `fullyFaithfulCoconstantSheaf`: `coconstantSheaf` is fully faithful.
* `fullyFaithfulConstantSheaf`: on local sites, the constant sheaf functor is fully faithful.
All together this shows that for local sites `Sheaf J (Type max u v w)` forms a local topos, but
since we don't yet have local topoi this can't be stated yet.

We also define a Grothendieck topology `localTopology C` on any category `C` with a terminal object,
and show that it is the largest topology making `C` into a local site.

TODO: generalise universe levels from `max u v` to `max u v w` again once that is possible.
-/

universe u v w

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A local site is a site that has a terminal object with only a single covering sieve. -/
class GrothendieckTopology.IsLocalSite extends HasTerminal C where
  /-- The only covering sieve of the terminal object is the trivial sieve. -/
  eq_top_of_mem : ∀ S ∈ J (⊤_ C), S = ⊤

/-- On a local site, every covering sieve contains every morphism from the terminal object. -/
lemma LocalSite.from_terminal_mem_of_mem [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
    (hS : S ∈ J X) : S.arrows f :=
  (S.mem_iff_pullback_eq_top f).2 <| IsLocalSite.eq_top_of_mem _ <| J.pullback_stable f hS

/-- Every category with a terminal object becomes a local site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : (trivial C).IsLocalSite where
  eq_top_of_mem _ := trivial_covering.1

/-- The functor that sends any type `A` to the functor `Cᵒᵖ → Type _` that sends any `X : C`
to the type of all functions `(⊤_ C ⟶ X) → A`. This can be defined on any site with a terminal
object, but has values in sheaves in the case of local sites. -/
noncomputable def Presheaf.coconst {C : Type u} [Category.{v} C] [HasTerminal C] :
    Type w ⥤ (Cᵒᵖ ⥤ Type max v w) :=
  uliftFunctor ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
    (coyoneda.obj (op (⊤_ C)) ⋙ uliftFunctor).op

/-- On local sites, `Presheaf.coconst` actually takes values in sheaves. -/
lemma Presheaf.coconst_isSheaf [J.IsLocalSite] (X : Type w) : IsSheaf J (coconst.obj X) := by
  refine (isSheaf_iff_isSheaf_of_type J _).2 fun Y S hS f hf ↦ ?_
  refine ⟨fun g ↦ f g.down (LocalSite.from_terminal_mem_of_mem J g.down hS) ⟨𝟙 _⟩, ?_, ?_⟩
  · intro Z g hg
    exact funext fun (x : ULift (_ ⟶ _)) ↦
      (congrFun (f.comp_of_compatible S hf hg x.down) _).trans (congrArg (f g hg) <| by simp)
  · intro g hg
    exact funext fun h : ULift (⊤_ C ⟶ Y) ↦ Eq.trans (by simp [Presheaf.coconst]) <|
      congrFun (hg h.down ((LocalSite.from_terminal_mem_of_mem J h.down hS))) _

/-- The right adjoint to the global sections functor that exists over any local site.
Takes a type `X` to the sheaf that sends each `Y : C` to the type of functions `Y → X`. -/
noncomputable def IsLocalSite.coconstantSheaf [J.IsLocalSite] :
    Type w ⥤ Sheaf J (Type (max v w)) where
  obj X := ⟨Presheaf.coconst.obj X, Presheaf.coconst_isSheaf J X⟩
  map f := ⟨Presheaf.coconst.map f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

-- this is currently needed to obtain the instance `HasSheafify J (Type max u v)`.
attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

/-- On local sites, the global sections functor `Γ` is left-adjoint to the coconstant functor. -/
@[simps!]
noncomputable def IsLocalSite.ΓCoconstantSheafAdj [J.IsLocalSite] :
    Γ J (Type max u v) ⊣ coconstantSheaf J := by
  refine Adjunction.ofNatIsoLeft ?_ (ΓNatIsoSheafSections J _ terminalIsTerminal).symm
  exact {
    unit := {
      app X := ⟨{
        app Y (x : X.val.obj Y) y := ⟨X.val.map (op y.down) x⟩
        naturality Y Z f := by
          ext (x : X.val.obj Y); dsimp [coconstantSheaf, Presheaf.coconst]; ext z
          exact (FunctorToTypes.map_comp_apply X.val _ _ x).symm
      }⟩
      naturality X Y f := by
        ext Z (x : X.val.obj Z); dsimp [coconstantSheaf, Presheaf.coconst]; ext z
        exact (NatTrans.naturality_apply f.val _ x).symm
    }
    counit := { app X := fun f : ULift (_ ⟶ _) → _ ↦ (f default).down }
    left_triangle_components X := by
      ext (x : X.val.obj _)
      dsimp; convert congrFun (X.val.map_id _) x; exact Subsingleton.elim _ _
    right_triangle_components X := by
      ext Y (f : _ → _); dsimp [coconstantSheaf, Presheaf.coconst]; ext y
      dsimp; congr; convert Category.id_comp _; exact Subsingleton.elim _ _
  }

instance [J.IsLocalSite] : (IsLocalSite.coconstantSheaf.{u,v,max u v} J).IsRightAdjoint :=
  ⟨Γ J _, ⟨IsLocalSite.ΓCoconstantSheafAdj J⟩⟩

instance [J.IsLocalSite] : HasCoconstantSheaf J (Type max u v) :=
  ⟨_, ⟨IsLocalSite.ΓCoconstantSheafAdj J⟩⟩

/-- The global sections of the coconstant sheaf on a type are naturally isomorphic to that type.-/
noncomputable def coconstantSheafΓNatIsoId [J.IsLocalSite] :
    IsLocalSite.coconstantSheaf J ⋙ Γ J _ ≅ 𝟭 (Type max u v) := by
  refine (Functor.isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)).trans ?_
  exact (NatIso.ofComponents (fun X ↦ {
    hom x := fun _ ↦ ⟨x⟩
    inv f := (f (default : ULift (⊤_ C ⟶ ⊤_ C))).down
    inv_hom_id := by
      dsimp [IsLocalSite.coconstantSheaf, Presheaf.coconst]; ext; dsimp
      congr; exact Subsingleton.elim _ _
  })).symm

/-- `coconstantSheaf` is fully faithful. -/
noncomputable def fullyFaithfulCoconstantSheaf [J.IsLocalSite] :
    (IsLocalSite.coconstantSheaf.{u,v,max u v} J).FullyFaithful :=
  (IsLocalSite.ΓCoconstantSheafAdj J).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId J)

instance [J.IsLocalSite] : (IsLocalSite.coconstantSheaf.{u,v,max u v} J).Full :=
  (fullyFaithfulCoconstantSheaf J).full

instance [J.IsLocalSite] : (IsLocalSite.coconstantSheaf.{u,v,max u v} J).Faithful :=
  (fullyFaithfulCoconstantSheaf J).faithful

/-- On local sites, the constant sheaf functor is fully faithful. -/
noncomputable def fullyFaithfulConstantSheaf [HasWeakSheafify J (Type max u v)] [J.IsLocalSite] :
    (constantSheaf J (Type max u v)).FullyFaithful :=
  (Adjunction.Triple.mk (constantSheafΓAdj J _)
    (IsLocalSite.ΓCoconstantSheafAdj J)).fullyFaithfulEquiv.symm <| fullyFaithfulCoconstantSheaf J

instance [HasWeakSheafify J (Type max u v)] [J.IsLocalSite] :
    (constantSheaf J (Type max u v)).Full :=
  (fullyFaithfulConstantSheaf J).full

instance [HasWeakSheafify J (Type max u v)] [J.IsLocalSite] :
    (constantSheaf J (Type max u v)).Faithful :=
  (fullyFaithfulConstantSheaf J).faithful

/-- The largest topology making a category with a terminal object a local site.
Lacking an established name, we call it the local topology. -/
def localTopology (C : Type*) [Category C] [HasTerminal C] : GrothendieckTopology C :=
  (MorphismProperty.morphismsThrough (⊤_ C)).generatedTopology

lemma localTopology.mem_sieves_iff [HasTerminal C] {X : C} {S : Sieve X} :
    S ∈ localTopology C X ↔ ∀ x : ⊤_ C ⟶ X, S x :=
  ⟨fun hS x ↦ (MorphismProperty.toSieveOn_le_iff _).1 hS _ x ⟨𝟙 _, x, by simp⟩, fun hS ↦
    (MorphismProperty.toSieveOn_le_iff _).2 fun Y f ⟨g, g', hf⟩ ↦ hf ▸ S.downward_closed (hS _) _⟩

open List in
/-- For any site with a terminal object, the following are equivalent:
* the site is local, i.e. the only covering sieve of the terminal object is the trivial one
* every covering sieve contains all morphisms from the terminal object
* the coconstant presheaf on the empty type is a sheaf
* every coconstant presheaf is a sheaf.

I don't yet know how exactly `HasCoconstantSheaf J (Type max u v)` fits into this - every
local site has a coconstant sheaf functor, and every *subcanonical* site with a coconstant sheaf
functor is local, but it's not clear to me what can be said in the non-subcanonical case. Maybe
having a fully faithful coconstant sheaf functor could be strong enough?
TODO: figure this out -/
protected theorem GrothendieckTopology.IsLocalSite.tfae [HasTerminal C] :
    TFAE [J.IsLocalSite,
      ∀ X : C, ∀ S ∈ J X, ∀ x : ⊤_ C ⟶ X, S x,
      J ≤ localTopology C,
      Presieve.IsSheaf J (Presheaf.coconst.{u,v,max u v}.obj PEmpty),
      ∀ X : Type max u v, Presieve.IsSheaf J (Presheaf.coconst.obj X)] := by
  tfae_have 2 → 1 := fun h ↦ ⟨fun S hS ↦ S.id_mem_iff_eq_top.1 <| h _ S hS _⟩
  tfae_have 1 → 2 := fun h X S hS f ↦ by
    simpa using Sieve.id_mem_iff_eq_top.2 <| h.eq_top_of_mem _ <| J.pullback_stable f hS
  tfae_have 3 ↔ 2 := by simp_rw [← localTopology.mem_sieves_iff]; rfl
  tfae_have 4 → 1 := fun h ↦ ⟨fun S hS ↦ by
    replace h : IsEmpty (Presieve.FamilyOfElements
        (Presheaf.coconst.{u,v,max u v}.obj PEmpty) S.arrows) := by
      have : IsEmpty ((Presheaf.coconst.{u,v,max u v}.obj PEmpty).obj (op (⊤_ C))) := by
        dsimp [Presheaf.coconst]; exact isEmpty_fun.2 ⟨⟨⟨𝟙 _⟩⟩, inferInstance⟩
      have {X : C} : Subsingleton ((Presheaf.coconst.{u,v,max u v}.obj PEmpty).obj (op X)) := by
        dsimp [Presheaf.coconst]; exact Pi.instSubsingleton
      refine not_nonempty_iff.1 fun ⟨x⟩ ↦ IsEmpty.false (h S hS x ?_).choose
      exact fun _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _
    replace ⟨X, f, hf, h⟩ : ∃ X, ∃ f : X ⟶ ⊤_ C, S f ∧
        IsEmpty ((Presheaf.coconst.{u,v,max u v}.obj PEmpty).obj (op X)) := by
      by_contra! h'; exact h.false fun X f hf ↦ Classical.choice <| not_isEmpty_iff.1 <| h' X f hf
    let ⟨⟨(g : _ ⟶ _)⟩⟩ := (isEmpty_fun.1 h).1
    refine S.id_mem_iff_eq_top.1 ?_
    convert S.downward_closed hf g
    exact Subsingleton.elim _ _⟩
  tfae_have 5 → 4 := fun h ↦ h _
  tfae_have 1 → 5 := fun _ _ ↦ (isSheaf_iff_isSheaf_of_type _ _).1 <| Presheaf.coconst_isSheaf J _
  tfae_finish

instance [HasTerminal C] : (localTopology C).IsLocalSite :=
  ((GrothendieckTopology.IsLocalSite.tfae _).out 0 2).2 le_rfl

end CategoryTheory
