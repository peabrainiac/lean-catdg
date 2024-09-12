import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Topology.Category.TopCat.Basic
import Orbifolds.Diffeology.DDiffeomorph

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
* `DiffCat.discreteForgetAdj`, `DiffCat.forgetIndiscreteAdj`: the adjunctions
  `discrete ⊣ forget ⊣ indiscrete`.
* `DiffCat.hasLimits`, `DiffCat.hasColimits`: `DiffCat` is complete and cocomplete.
* `DiffCat.forgetPreservesLimits`, `DiffCat.forgetPreservesColimits`: the forgetful functor
  `DiffCat ⥤ Type` preserves limits and colimits.
-/

open CategoryTheory

open Topology

universe u v

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

namespace DiffCat

/-!
### Limits and colimits

The category of diffeological spaces is complete and cocomplete, and the forgetful functor
preserves all limits and colimits. Adapted from `Mathlib.Topology.Category.TopCat.Limits`.
-/
section Limits

open CategoryTheory.Limits

variable {J : Type v} [SmallCategory J]

local notation "forget" => forget DiffCat

/-- A specific choice of limit cone for any `F : J ⥤ DiffCat`. -/
def limitCone (F : J ⥤ DiffCat.{max v u}) : Cone F where
  pt := of { u : (j : J) → F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j => ⟨fun u => u.val j,DSmooth.comp (dsmooth_apply _) (dsmooth_subtype_val)⟩
      naturality := fun X Y f => by
        dsimp [Category.id_comp]
        exact DSmoothMap.ext fun a => (a.2 f).symm }

/-- `DiffCat.limitCone F` is actually a limit cone for the given `F : J ⥤ DiffCat`. -/
def limitConeIsLimit (F : J ⥤ DiffCat.{max v u}) : IsLimit (limitCone.{u,v} F) where
  lift S :=
    ⟨fun x => ⟨fun j => S.π.app _ x, fun f => by dsimp; exact S.w f ▸ rfl⟩,
    DSmooth.subtype_mk (dsmooth_pi fun j => (S.π.app j).2) fun x i j f => by
      dsimp; exact S.w f ▸ rfl⟩
  fac S j := by dsimp [limitCone]; rfl
  uniq S m h := DSmoothMap.ext fun a => Subtype.ext <| by simp_rw [← h]; rfl

instance hasLimitsOfSize : HasLimitsOfSize.{v,v} DiffCat.{max u v} where
  has_limits_of_shape _ := ⟨fun F => HasLimit.mk ⟨limitCone.{u,v} F,limitConeIsLimit F⟩⟩

/-- `DiffCat` has all limits, i.e. it is complete. -/
instance hasLimits : HasLimits DiffCat.{u} :=
  hasLimitsOfSize.{u,u}

noncomputable instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize forget :=
  ⟨⟨fun {F} => preservesLimitOfPreservesLimitCone (limitConeIsLimit.{u,v} F)
      (Types.limitConeIsLimit.{v,u} (F ⋙ forget))⟩⟩

/-- The forgetful functor `DiffCat ⥤ Type` preserves all limits. -/
noncomputable instance forgetPreservesLimits : PreservesLimits forget :=
  forgetPreservesLimitsOfSize.{u,u}

/-- A specific choice of colimit cocone for any `F : J ⥤ DiffCat`. -/
noncomputable def colimitCocone (F : J ⥤ DiffCat.{max v u}) : Cocone F where
  pt := ⟨(Types.TypeMax.colimitCocone.{v,u} (F ⋙ forget)).pt,
          ⨆ j, (F.obj j).str.coinduced ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j)⟩
  ι :=
    { app := fun j =>
        ⟨(Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j, dsmooth_iff_coinduced_le.mpr <|
          le_iSup (fun j => DiffeologicalSpace.coinduced
            ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j) (F.obj j).str) j⟩
      naturality := fun _ _ f =>
        DSmoothMap.coe_injective ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.naturality f) }


/-- `DiffCat.colimitCocone F` is actually a colimit cocone for the given `F : J ⥤ DiffCat`. -/
def colimitCoconeIsColimit (F : J ⥤ DiffCat.{max v u}) : IsColimit (colimitCocone F) := by
  refine IsColimit.ofFaithful forget (Types.TypeMax.colimitCoconeIsColimit.{v,u} _) (fun s =>
      ⟨Quot.lift (fun p => (Functor.mapCocone forget s).ι.app p.fst p.snd) ?_, ?_⟩) fun s => rfl
  · intro _ _ ⟨_, h⟩; simp [h,←comp_apply',s.ι.naturality]
  · exact dsmooth_iff_le_induced.mpr
      (iSup_le fun j => DiffeologicalSpace.coinduced_le_iff_le_induced.mp <|
        DiffeologicalSpace.coinduced_compose.symm ▸ (s.ι.app j).dsmooth.coinduced_le)

instance hasColimitsOfSize : HasColimitsOfSize.{v,v} DiffCat.{max v u} where
  has_colimits_of_shape _ := ⟨fun F => HasColimit.mk ⟨colimitCocone F,colimitCoconeIsColimit F⟩⟩

/-- `DiffCat` has all colimits, i.e. it is cocomplete. -/
instance hasColimits : HasColimits DiffCat.{u} :=
  hasColimitsOfSize.{u,u}

noncomputable instance forgetPreservesColimitsOfSize : PreservesColimitsOfSize forget :=
  ⟨⟨fun {F} => preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u,v} F)
    (Types.TypeMax.colimitCoconeIsColimit.{v,u} (F ⋙ forget))⟩⟩

/-- The forgetful functor `DiffCat ⥤ Type` preserves all colimits. -/
noncomputable instance forgetPreservesColimits : PreservesColimits forget :=
  forgetPreservesColimitsOfSize.{u,u}

end Limits

/-!
### Products
Products in `DiffCat` are given by the usual products of spaces.
Adapted from `Mathlib.CategoryTheory.Limits.Shapes.Types`.
-/
section BinaryProducts

open Limits WalkingPair

/-- The product space `X × Y` as a cone. -/
def binaryProductCone (X Y : DiffCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk (P := of (X × Y)) ⟨_,dsmooth_fst⟩ ⟨_,dsmooth_snd⟩

/-- `DiffCat.binaryProductCone X Y` is actually a limiting cone. -/
def binaryProductLimit (X Y : DiffCat.{u}) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) := ⟨_,s.fst.dsmooth.prod_mk s.snd.dsmooth⟩
  fac _ j := Discrete.recOn j fun j => by cases' j <;> rfl
  uniq s f w := DSmoothMap.ext fun x => Prod.ext
    (congrFun (congrArg DSmoothMap.toFun (w ⟨left⟩)) x)
    (congrFun (congrArg DSmoothMap.toFun (w ⟨right⟩)) x)

/-- The functor taking `X`, `Y` to the product space `X × Y`. -/
def binaryProductFunctor : DiffCat.{u} ⥤ DiffCat.{u} ⥤ DiffCat.{u} where
  obj X := {
    obj := fun Y => of (X × Y)
    map := fun {Y Y'} f => ⟨_,dsmooth_id.prod_map f.dsmooth⟩ }
  map {X Y} f := {
    app := fun Z => ⟨_,f.dsmooth.prod_map dsmooth_id⟩
    naturality := fun {X' Y'} f' => rfl }
  map_id := fun X => rfl
  map_comp := fun {X Y Z} f g => rfl

/-- The explicit products we defined are naturally isomorphic to the products coming from
  the `HasLimits` instance on diffcat. This is needed because the `HasLimits`
  instance only stores proof that all limits exist, not the explicit constructions,
  so the products derived from it are picked with the axiom of choice. -/
noncomputable def binaryProductIsoProd : binaryProductFunctor.{u} ≅ (prod.functor) := by
  refine' NatIso.ofComponents (fun X => _) (fun _ => _)
  · refine' NatIso.ofComponents (fun Y => _) (fun _ => _)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply prod.hom_ext <;> simp <;> rfl
  · ext : 2; apply prod.hom_ext <;> simp <;> rfl

end BinaryProducts

section Cartesian

noncomputable instance : MonoidalCategory DiffCat := monoidalOfHasFiniteProducts DiffCat

/-- `DiffCat` is cartesian-closed. -/
noncomputable instance cartesianClosed : CartesianClosed DiffCat.{u} where
  closed X := ⟨⟨{
      obj := fun Y => DiffCat.of (DSmoothMap X Y)
      map := fun f => ⟨f.comp,DSmoothMap.dsmooth_comp.curry_right⟩
    },(by exact Adjunction.mkOfHomEquiv {
      homEquiv := fun Y Z => (DDiffeomorph.prodComm.comp_right).toEquiv.trans
        (@DDiffeomorph.curry Y X Z _ _ _).toEquiv
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl
    } : Adjunction _ _).ofNatIsoLeft <| binaryProductIsoProd.app X⟩⟩

#print axioms cartesianClosed

end Cartesian

end DiffCat
