import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!
# Global sections of sheaves
-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A]

/-- The global sections functor `Γ`, taking sheaves valued in `A` to its global sections in `A`.
It is given here as a limit instead of evaluation on a terminal object of `C`; this has the
advantage of not requiring `C` to have a terminal object, but the disadvantage of requiring `A`
to have limits of shape `Cᵒᵖ`. -/
noncomputable def Sheaf.Γ [HasLimitsOfShape Cᵒᵖ A] : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ lim

/-- The constant sheaf functor is left-adjoint to the global sections functor when both exist. -/
noncomputable def constantSheafΓAdj [HasWeakSheafify J A] [HasLimitsOfShape Cᵒᵖ A] :
    constantSheaf J A ⊣ Γ J A :=
  constLimAdj.comp (sheafificationAdjunction J A)

/-- The sheaf sections functor on `X` is given by evaluation of presheaves on `X`.
TODO: move somewhere else -/
def sheafSectionsNatIsoEvaluation {X : C} :
    (sheafSections J A).obj (op X) ≅ sheafToPresheaf J A ⋙ (evaluation _ _).obj (op X) :=
  NatIso.ofComponents fun _ ↦ eqToIso rfl

/-- Evaluating a terminal functor yields terminal objects. -/
noncomputable def Limits.IsTerminal.isTerminalObj_functor {C : Type u} [Category.{v} C]
    {D : Type u₂} [Category.{v₂} D] [HasLimits D] {F : C ⥤ D} (hF : IsTerminal F) (X : C) :
    IsTerminal (F.obj X) :=
  hF.isTerminalObj ((evaluation C D).obj X)

#check Types.isTerminalEquivUnique

/-- The limit of a functor `F : C ⥤ Type u` is naturally isomorphic to the type of morphisms
from the terminal functor to `F`.
TODO: move somewhere else -/
noncomputable def limNatIsoCoyoneda : (lim : (C ⥤ Type u) ⥤ _) ≅ coyoneda.obj (op (⊤_ _)) := by
  exact NatIso.ofComponents fun F ↦ by
    --refine (limit.isLimit _).conePointUniqueUpToIso <| ?_
    let _ : ∀ X, Unique ((⊤_ (C ⥤ Type u)).obj X) := fun X ↦ (terminalIsoIsTerminal <|
      terminalIsTerminal.isTerminalObj_functor X).symm.toEquiv.unique
    let c : Cone F := {
      pt := ⊤_ (C ⥤ Type u) ⟶ F--(coyoneda.obj (op (⊤_ (C ⥤ Type u)))).obj F
      π := {
        app X := fun α : _ ⟶ _ ↦ α.app _ default
        naturality X Y f := funext fun α ↦
          (congrArg _ (Unique.default_eq _)).trans <| NatTrans.naturality_apply α f _
      }
    }
    let _ : IsLimit c := by sorry
    sorry

/-- When `C` has a terminal object, the global sections functor is isomorphic to the functor
of sections on that object. -/
noncomputable def Sheaf.ΓNatIsoSheafSections [HasLimitsOfShape Cᵒᵖ A] {T : C}
    (hT : IsTerminal T) : Γ J A ≅ (sheafSections J A).obj (op T) := by
  refine (isoWhiskerLeft _ ?_).trans <| (sheafSectionsNatIsoEvaluation J A).symm
  refine @asIso _ _ _ _ { app := fun F ↦ limit.π _ _ } ?_
  have hT' := initialOpOfTerminal hT
  exact (NatTrans.isIso_iff_isIso_app _).2 <| fun F ↦ isIso_π_of_isInitial hT' F

/-- For sheaves of types, the global sections functor is isomorphic to the covariant hom
functor of the terminal sheaf. -/
noncomputable def Sheaf.ΓNatIsoCoyonedaObj :
    Γ J (Type u) ≅ coyoneda.obj (op (⊤_ _)) := by
  refine (isoWhiskerLeft _ limNatIsoCoyoneda).trans <| ?_
  let e : (⊤_ Sheaf J _).val ≅ ⊤_ Cᵒᵖ ⥤ Type u :=
    (terminalIsoIsTerminal (terminalIsTerminal.isTerminalObj (sheafToPresheaf J _) _)).symm
  refine (isoWhiskerLeft _ <| coyoneda.mapIso e.op).trans ?_
  exact NatIso.ofComponents fun _ ↦ Sheaf.homEquiv.toIso.symm

end CategoryTheory
