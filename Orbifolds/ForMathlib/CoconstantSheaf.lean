import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Coconstant sheaves
In this file we define a *coconstant sheaf functor* `A ⥤ Sheaf J A` as a right adjoint to the
global sections functor `Γ : Sheaf J A ⥤ A` when one exists.
-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A] [HasGlobalSectionsFunctor J A]

/-- Typeclass stating that the global sections functor has a right adjoint. This right adjoint will
then be called the coconstant sheaf functor and written `coconstantSheaf J A`. -/
abbrev HasCoconstantSheaf := (Γ J A).IsLeftAdjoint

/-- We define the coconstant sheaf functor as the right-adjoint of the global sections functor
whenever it exists. -/
noncomputable def coconstantSheaf [HasCoconstantSheaf J A] : A ⥤ Sheaf J A :=
  (Γ J A).rightAdjoint

/-- The global sections functor is by definition left-adjoint to the coconstant sheaf functor
whenever both exist. -/
noncomputable def ΓCoconstantSheafAdj [HasCoconstantSheaf J A] :
    Γ J A ⊣ coconstantSheaf J A :=
  .ofIsLeftAdjoint _

instance [HasCoconstantSheaf J A] : (coconstantSheaf J A).IsRightAdjoint := by
  unfold coconstantSheaf; infer_instance

instance [HasCoconstantSheaf J A] [(constantSheaf J A).Full] [(constantSheaf J A).Faithful] :
    (coconstantSheaf J A).Full :=
  ((constantSheafΓAdj J A).fullyFaithfulEquiv (ΓCoconstantSheafAdj J A) (.ofFullyFaithful _)).full

instance [HasCoconstantSheaf J A] [(constantSheaf J A).Full] [(constantSheaf J A).Faithful] :
    (coconstantSheaf J A).Faithful :=
  ((constantSheafΓAdj J A).fullyFaithfulEquiv
    (ΓCoconstantSheafAdj J A) (.ofFullyFaithful _)).faithful
