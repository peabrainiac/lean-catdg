import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Orbifolds.Diffeology.Constructions

/-!
# Category of diffeological spaces
The category of diffeological spaces and smooth maps.
Adapted from `Mathlib.Topology.Category.TopCat.Basic`.

Main definitions / results:
* `DiffCat`: the category of diffeological spaces and smooth maps.
* `forget DiffCat`: the forgetful functor `DiffCat ⥤ Type`,
  provided through a `ConcreteCategory`-instance on `DiffCat`.
* `DiffCat.discrete`, `DiffCat.indiscrete`: the functors `Type ⥤ DiffCat` giving each type the
  discrete/indiscrete diffeology.
* `DiffCat.dTop`: the functor `DiffCat ⥤ TopCat` giving each space its D-topology.
* `discreteForgetAdj`, `forgetIndiscreteAdj`: the adjunctions `discrete ⊣ forget ⊣ indiscrete`.
-/

open CategoryTheory

open Topology

universe u

/-!
### Bundled smooth maps

The type of smooth maps between two diffeological spaces.
-/

section DSmoothMap

def DSmoothMap (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] :=
  {f : X → Y // DSmooth f}

namespace DSmoothMap

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

instance instFunLike : FunLike (DSmoothMap X Y) X Y where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

protected def toFun (f : DSmoothMap X Y) : X → Y := f.val

protected lemma dsmooth (f : DSmoothMap X Y) : DSmooth f := f.prop

@[simp]
lemma toFun_eq_coe {f : DSmoothMap X Y} : f.toFun = (f : X → Y) := rfl

@[ext]
lemma ext {f g : DSmoothMap X Y} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

nonrec def id : DSmoothMap X X := ⟨id,dsmooth_id⟩

def comp (f : DSmoothMap Y Z) (g : DSmoothMap X Y) : DSmoothMap X Z :=
  ⟨f ∘ g, (f.dsmooth).comp g.dsmooth⟩

end DSmoothMap

end DSmoothMap

/-!
### DiffCat

Basic definitions and lemmas about the category of diffeological spaces.
-/

section Basic

@[to_additive existing DiffCat]
def DiffCat : Type (u + 1) :=
  Bundled DiffeologicalSpace

namespace DiffCat

instance bundledHom : BundledHom @DSmoothMap where
  toFun := @DSmoothMap.toFun
  id := @DSmoothMap.id
  comp := @DSmoothMap.comp

deriving instance LargeCategory for DiffCat

instance concreteCategory : ConcreteCategory DiffCat :=
  inferInstanceAs <| ConcreteCategory (Bundled DiffeologicalSpace)

instance : CoeSort DiffCat Type* where
  coe X := X.α

instance topologicalSpaceUnbundled (X : DiffCat) : DiffeologicalSpace X :=
  X.str

instance instFunLike (X Y : DiffCat) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (DSmoothMap X Y) X Y

-- TODO DSmoothMapClass-Instanz

lemma id_app (X : DiffCat) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

lemma comp_app {X Y Z : DiffCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

@[simp]
lemma coe_id (X : DiffCat) : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : DiffCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma hom_inv_id_apply {X Y : DiffCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  DFunLike.congr_fun f.hom_inv_id x

@[simp]
lemma inv_hom_id_apply {X Y : DiffCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  DFunLike.congr_fun f.inv_hom_id y

/-- Construct a bundled space from the underlying type and the typeclass. -/
def of (X : Type u) [DiffeologicalSpace X] : DiffCat :=
  ⟨X, inferInstance⟩

@[instance] abbrev diffeologicalSpace_forget
    (X : DiffCat) : DiffeologicalSpace <| (forget DiffCat).obj X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [DiffeologicalSpace X] : (of X : Type u) = X := rfl

-- TODO `coe_of_of`?

instance inhabited : Inhabited DiffCat :=
  ⟨Empty,⊥⟩

def discrete : Type u ⥤ DiffCat.{u} where
  obj X := ⟨X,⊥⟩
  map f := ⟨f,dsmooth_bot⟩

def indiscrete : Type u ⥤ DiffCat.{u} where
  obj X := ⟨X,⊤⟩
  map f := ⟨f,dsmooth_top⟩

def dTop : DiffCat.{u} ⥤ TopCat.{u} where
  obj X := ⟨X,DTop⟩
  map f := ⟨f,f.dsmooth.continuous⟩

/-- Adjunction `discrete ⊣ forget`, adapted from
  `Mathlib.Topology.Category.TopCat.Adjunctions`. -/
@[simps! unit counit]
def discreteForgetAdj : discrete ⊣ forget DiffCat.{u} :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun X => id }
      counit := { app := fun X => ⟨id, dsmooth_bot⟩ } }

/-- Adjunction `forget ⊣ indiscrete`, adapted from
  `Mathlib.Topology.Category.TopCat.Adjunctions`. -/
@[simps! unit counit]
def forgetIndiscreteAdj : forget DiffCat.{u} ⊣ indiscrete :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun X => ⟨id, dsmooth_top⟩ }
      counit := { app := fun X => id } }

instance : IsRightAdjoint (forget DiffCat.{u}) :=
  ⟨_, discreteForgetAdj⟩

instance : IsLeftAdjoint (forget DiffCat.{u}) :=
  ⟨_, forgetIndiscreteAdj⟩

end DiffCat

end Basic
