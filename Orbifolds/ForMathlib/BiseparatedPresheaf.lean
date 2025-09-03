import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Biseparated presheaves
On any category with a two Grothendieck topologies `J` and `K`, we define the category `Bisep J K`
of all presheaves that are sheaves with respect to `J` and separated with respect to `K`, and show
that it is a reflective subcategory (TODO). Important examples (though not worked out in this file)
are the categories of diffeological spaces, quasitopological spaces and simplicial complexes.

See https://ncatlab.org/nlab/show/separated+presheaf#biseparated_presheaf and section C.2.2 of
*Sketches of an Elephant*.
-/

universe u v w

open CategoryTheory Category Sheaf GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J K : GrothendieckTopology C)

/-- The category of biseparated presheaves with respect to `J` and `K`, i.e. of all presheaves that
are sheaves with respect to `J` and separated with respect to `K`. -/
structure Bisep where
  /-- The underlying presheaf. -/
  val : Cᵒᵖ ⥤ Type w
  /-- The underlying presheaf is a sheaf with respect to `J`. -/
  isSheaf : Presheaf.IsSheaf J val
  /-- The underlying presheaf is separated with respect to `K`. -/
  isSeparated : Presieve.IsSeparated K val

variable {J K}

/-- Morphisms of biseparated presheaves are just morphisms of their underlying presheaves. -/
@[ext]
structure Bisep.Hom (X Y : Bisep J K) where
  /-- The underlying morphism of presheaves. -/
  val : X.val ⟶ Y.val

@[simps id_val comp_val]
instance Bisep.instCategory : Category (Bisep J K) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩
  id_comp _ := Hom.ext <| id_comp _
  comp_id _ := Hom.ext <| comp_id _
  assoc _ _ _ := Hom.ext <| assoc _ _ _

/-- The sheaf (with respect to `J`) underlying a biseparated presheaf. -/
@[simps]
def Bisep.toSheaf (P : Bisep J K) : Sheaf J (Type w) := ⟨P.val, P.isSheaf⟩

variable (J K) in
/-- The inclusion functor from biseparated presheaves to sheaves. -/
@[simps]
def bisepToSheaf : Bisep J K ⥤ Sheaf J (Type w) where
  obj P := P.toSheaf
  map f := ⟨f.val⟩

variable (J K) in
/-- The inclusion functor from biseparated presheaves to sheaves is fully faithful. -/
def fullyFaithfulBisepToSheaf : (bisepToSheaf J K).FullyFaithful where
  preimage f := ⟨f.val⟩

instance : (bisepToSheaf J K).Full :=
  (fullyFaithfulBisepToSheaf J K).full

instance : (bisepToSheaf J K).Faithful :=
  (fullyFaithfulBisepToSheaf J K).faithful

instance : (bisepToSheaf J K).ReflectsIsomorphisms :=
  (fullyFaithfulBisepToSheaf J K).reflectsIsomorphisms

end CategoryTheory
