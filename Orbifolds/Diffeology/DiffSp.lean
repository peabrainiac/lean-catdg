import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Topology.Category.TopCat.Basic
import Orbifolds.Diffeology.DDiffeomorph
import Orbifolds.Diffeology.Continuous
import Orbifolds.ForMathlib.DeltaGenerated

/-!
# Category of diffeological spaces
The category of diffeological spaces and smooth maps.
Adapted from `Mathlib.Topology.Category.TopCat.Basic`.

Main definitions / results:
* `DiffSp`: the category of diffeological spaces and smooth maps.
* `forget DiffSp`: the forgetful functor `DiffSp ⥤ Type`,
  provided through a `ConcreteCategory`-instance on `DiffSp`.
* `DiffSp.discrete`, `DiffSp.indiscrete`: the functors `Type ⥤ DiffSp` giving each type the
  discrete/indiscrete diffeology.
* `DiffSp.discreteForgetAdj`, `DiffSp.forgetIndiscreteAdj`: the adjunctions
  `discrete ⊣ forget ⊣ indiscrete`.
* `DiffSp.dTop`, `DiffSp.diffToDeltaGenerated`, `DiffSp.topToDiff`,
  `DiffSp.deltaGeneratedToDiff`: the functors between `DiffSp`, `DeltaGenerated` and
  `TopCat` given by the D-topology and continuous diffeology.
* `DiffSp.dTopAdj`, `DiffSp.dTopAdj'`: the adjunctions between those.
* `DiffSp.hasLimits`, `DiffSp.hasColimits`: `DiffSp` is complete and cocomplete.
* `DiffSp.forgetPreservesLimits`, `DiffSp.forgetPreservesColimits`: the forgetful functor
  `DiffSp ⥤ Type` preserves limits and colimits.
-/

open CategoryTheory

open Topology

universe u v

/-!
### DiffSp

Basic definitions and lemmas about the category of diffeological spaces.
-/

section Basic

@[to_additive existing DiffSp]
def DiffSp : Type (u + 1) :=
  Bundled DiffeologicalSpace

namespace DiffSp

instance bundledHom : BundledHom @DSmoothMap where
  toFun := @DSmoothMap.toFun
  id := @DSmoothMap.id
  comp := @DSmoothMap.comp

deriving instance LargeCategory for DiffSp

instance concreteCategory : ConcreteCategory DiffSp :=
  inferInstanceAs <| ConcreteCategory (Bundled DiffeologicalSpace)

instance : CoeSort DiffSp Type* where
  coe X := X.α

instance diffeologicalSpaceUnbundled (X : DiffSp) : DiffeologicalSpace X :=
  X.str

instance instFunLike (X Y : DiffSp) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike (DSmoothMap X Y) X Y

-- TODO DSmoothMapClass-Instanz

lemma id_app (X : DiffSp) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

lemma comp_app {X Y Z : DiffSp} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

@[simp]
lemma coe_id (X : DiffSp) : (𝟙 X : X → X) = id := rfl

@[simp]
lemma coe_comp {X Y Z : DiffSp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma hom_inv_id_apply {X Y : DiffSp} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  DFunLike.congr_fun f.hom_inv_id x

@[simp]
lemma inv_hom_id_apply {X Y : DiffSp} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  DFunLike.congr_fun f.inv_hom_id y

/-- Construct a bundled space from the underlying type and the typeclass. -/
def of (X : Type u) [DiffeologicalSpace X] : DiffSp :=
  ⟨X, inferInstance⟩

@[instance] abbrev diffeologicalSpace_forget
    (X : DiffSp) : DiffeologicalSpace <| (forget DiffSp).obj X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [DiffeologicalSpace X] : (of X : Type u) = X := rfl

-- TODO `coe_of_of`?

instance inhabited : Inhabited DiffSp :=
  ⟨Empty,⊥⟩

/-- The functor equipping each type with the discrete diffeology. -/
def discrete : Type u ⥤ DiffSp.{u} where
  obj X := ⟨X,⊥⟩
  map f := ⟨f,dsmooth_bot⟩

/-- The functor equipping each type with the indiscrete diffeology. -/
def indiscrete : Type u ⥤ DiffSp.{u} where
  obj X := ⟨X,⊤⟩
  map f := ⟨f,dsmooth_top⟩

/-- Adjunction `discrete ⊣ forget`, adapted from
  `Mathlib.Topology.Category.TopCat.Adjunctions`. -/
@[simps! unit counit]
def discreteForgetAdj : discrete ⊣ forget DiffSp.{u} :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun X ↦ id }
      counit := { app := fun X ↦ ⟨id, dsmooth_bot⟩ } }

/-- Adjunction `forget ⊣ indiscrete`, adapted from
  `Mathlib.Topology.Category.TopCat.Adjunctions`. -/
@[simps! unit counit]
def forgetIndiscreteAdj : forget DiffSp.{u} ⊣ indiscrete :=
  Adjunction.mkOfUnitCounit
    { unit := { app := fun X ↦ ⟨id, dsmooth_top⟩ }
      counit := { app := fun X ↦ id } }

instance : Functor.IsRightAdjoint (forget DiffSp.{u}) :=
  ⟨_, ⟨discreteForgetAdj⟩⟩

instance : Functor.IsLeftAdjoint (forget DiffSp.{u}) :=
  ⟨_, ⟨forgetIndiscreteAdj⟩⟩

/-- The functor sending each diffeological spaces to its D-topology. -/
def dTop : DiffSp.{u} ⥤ TopCat.{u} where
  obj X := ⟨X,DTop⟩
  map f := ⟨f,f.dsmooth.continuous⟩

/-- The functor sending each diffeological space to its D-topology, as a delta-generated
  space. -/
def diffToDeltaGenerated : DiffSp.{u} ⥤ DeltaGenerated.{u} where
  obj X := ⟨⟨X,DTop⟩,inferInstance⟩
  map f := ⟨f,f.dsmooth.continuous⟩

/-- The functor equipping each topological space with the continuous diffeology. -/
def topToDiff : TopCat.{u} ⥤ DiffSp.{u} where
  obj X := of (withContinuousDiffeology X)
  map f := ⟨f,f.2.dsmooth⟩

/-- The functor equipping each delta-generated space with the continuous diffeology. -/
def deltaGeneratedToDiff : DeltaGenerated.{u} ⥤ DiffSp.{u} where
  obj X := of (withContinuousDiffeology X)
  map f := ⟨f.1,f.2.dsmooth⟩

/-- Adjunction between the D-topology and continuous diffeology as functors between
  `DiffSp` and `TopCat`. -/
def dTopAdj : dTop ⊣ topToDiff :=
  Adjunction.mkOfUnitCounit {
    unit := { app := fun X ↦ ⟨id,dsmooth_id.continuous.dsmooth'⟩ }
    counit := { app := fun X ↦ ⟨id,continuous_iff_coinduced_le.mpr deltaGenerated_le⟩ } }

/-- Adjunction between the D-topology and continuous diffeology as functors between
  `DiffSp` and `DeltaGenerated`. -/
def dTopAdj' : diffToDeltaGenerated ⊣ deltaGeneratedToDiff :=
  Adjunction.mkOfUnitCounit {
    unit := { app := fun X ↦ ⟨id,dsmooth_id.continuous.dsmooth'⟩ }
    counit := { app := fun X ↦ ⟨id,continuous_iff_coinduced_le.mpr
      dTop_continuousDiffeology_eq_self.le⟩ } }

/-- The D-topology functor `DiffSp ⥤ TopCat` is a left-adjoint. -/
instance : Functor.IsLeftAdjoint (dTop.{u}) :=
  ⟨_, ⟨dTopAdj⟩⟩

/-- The D-topology functor `DiffSp ⥤ DeltaGenerated` is a left-adjoint. -/
instance : Functor.IsLeftAdjoint (diffToDeltaGenerated.{u}) :=
  ⟨_, ⟨dTopAdj'⟩⟩

end DiffSp

end Basic

namespace DiffSp

/-!
### Limits and colimits

The category of diffeological spaces is complete and cocomplete, and the forgetful functor
preserves all limits and colimits. Adapted from `Mathlib.Topology.Category.TopCat.Limits`.
-/
section Limits

open CategoryTheory.Limits

variable {J : Type v} [SmallCategory J]

local notation "forget" => forget DiffSp

/-- A specific choice of limit cone for any `F : J ⥤ DiffSp`. -/
def limitCone (F : J ⥤ DiffSp.{max v u}) : Cone F where
  pt := of { u : (j : J) → F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j ↦ ⟨fun u ↦ u.val j,DSmooth.comp (dsmooth_apply _) (dsmooth_subtype_val)⟩
      naturality := fun X Y f ↦ by
        dsimp [Category.id_comp]
        exact DSmoothMap.ext fun a ↦ (a.2 f).symm }

/-- `DiffSp.limitCone F` is actually a limit cone for the given `F : J ⥤ DiffSp`. -/
def limitConeIsLimit (F : J ⥤ DiffSp.{max v u}) : IsLimit (limitCone.{u,v} F) where
  lift S :=
    ⟨fun x ↦ ⟨fun j ↦ S.π.app _ x, fun f ↦ by dsimp; exact S.w f ▸ rfl⟩,
    DSmooth.subtype_mk (dsmooth_pi fun j ↦ (S.π.app j).2) fun x i j f ↦ by
      dsimp; exact S.w f ▸ rfl⟩
  fac S j := by dsimp [limitCone]; rfl
  uniq S m h := DSmoothMap.ext fun a ↦ Subtype.ext <| by simp_rw [← h]; rfl

instance hasLimitsOfSize : HasLimitsOfSize.{v,v} DiffSp.{max u v} where
  has_limits_of_shape _ := ⟨fun F ↦ HasLimit.mk ⟨limitCone.{u,v} F,limitConeIsLimit F⟩⟩

/-- `DiffSp` has all limits, i.e. it is complete. -/
instance hasLimits : HasLimits DiffSp.{u} :=
  hasLimitsOfSize.{u,u}

noncomputable instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v,v} (forget : DiffSp.{max v u} ⥤ _) :=
  ⟨⟨fun {F} ↦ preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{u,v} F)
      (Types.limitConeIsLimit.{v,u} (F ⋙ forget))⟩⟩

/-- The forgetful functor `DiffSp ⥤ Type` preserves all limits. -/
noncomputable instance forgetPreservesLimits : PreservesLimits (forget : DiffSp.{u} ⥤ _) :=
  forgetPreservesLimitsOfSize.{u,u}

/-- A specific choice of colimit cocone for any `F : J ⥤ DiffSp`. -/
noncomputable def colimitCocone (F : J ⥤ DiffSp.{max v u}) : Cocone F where
  pt := ⟨(Types.TypeMax.colimitCocone.{v,u} (F ⋙ forget)).pt,
          ⨆ j, (F.obj j).str.coinduced ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j)⟩
  ι :=
    { app := fun j ↦
        ⟨(Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j, dsmooth_iff_coinduced_le.mpr <|
          le_iSup (fun j ↦ DiffeologicalSpace.coinduced
            ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.app j) (F.obj j).str) j⟩
      naturality := fun _ _ f ↦
        DSmoothMap.coe_injective ((Types.TypeMax.colimitCocone (F ⋙ forget)).ι.naturality f) }


/-- `DiffSp.colimitCocone F` is actually a colimit cocone for the given `F : J ⥤ DiffSp`. -/
def colimitCoconeIsColimit (F : J ⥤ DiffSp.{max v u}) : IsColimit (colimitCocone F) := by
  refine IsColimit.ofFaithful forget (Types.TypeMax.colimitCoconeIsColimit.{v,u} _) (fun s ↦
      ⟨Quot.lift (fun p ↦ (Functor.mapCocone forget s).ι.app p.fst p.snd) ?_, ?_⟩) fun s ↦ rfl
  · intro _ _ ⟨_, h⟩; simp [h,←comp_apply',s.ι.naturality]
  · exact dsmooth_iff_le_induced.mpr
      (iSup_le fun j ↦ DiffeologicalSpace.coinduced_le_iff_le_induced.mp <|
        DiffeologicalSpace.coinduced_compose.symm ▸ (s.ι.app j).dsmooth.coinduced_le)

instance hasColimitsOfSize : HasColimitsOfSize.{v,v} DiffSp.{max v u} where
  has_colimits_of_shape _ := ⟨fun F ↦ HasColimit.mk ⟨colimitCocone F,colimitCoconeIsColimit F⟩⟩

/-- `DiffSp` has all colimits, i.e. it is cocomplete. -/
instance hasColimits : HasColimits DiffSp.{u} :=
  hasColimitsOfSize.{u,u}

noncomputable instance forgetPreservesColimitsOfSize :
    PreservesColimitsOfSize.{v,v} (forget : DiffSp.{max v u} ⥤ _) :=
  ⟨⟨fun {F} ↦ preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u,v} F)
    (Types.TypeMax.colimitCoconeIsColimit.{v,u} (F ⋙ forget))⟩⟩

/-- The forgetful functor `DiffSp ⥤ Type` preserves all colimits. -/
noncomputable instance forgetPreservesColimits : PreservesColimits (forget : DiffSp.{u} ⥤ _) :=
  forgetPreservesColimitsOfSize.{u,u}

end Limits

/-!
### Products
Products in `DiffSp` are given by the usual products of spaces.
Adapted from `Mathlib.CategoryTheory.Limits.Shapes.Types`.
-/
section BinaryProducts

open Limits WalkingPair

/-- The product space `X × Y` as a cone. -/
def binaryProductCone (X Y : DiffSp.{u}) : BinaryFan X Y :=
  BinaryFan.mk (P := of (X × Y)) ⟨_,dsmooth_fst⟩ ⟨_,dsmooth_snd⟩

/-- `DiffSp.binaryProductCone X Y` is actually a limiting cone. -/
def binaryProductLimit (X Y : DiffSp.{u}) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) := ⟨_,s.fst.dsmooth.prod_mk s.snd.dsmooth⟩
  fac _ j := Discrete.recOn j fun j ↦ by cases' j <;> rfl
  uniq s f w := DSmoothMap.ext fun x ↦ Prod.ext
    (congrFun (congrArg DSmoothMap.toFun (w ⟨left⟩)) x)
    (congrFun (congrArg DSmoothMap.toFun (w ⟨right⟩)) x)

/-- The functor taking `X`, `Y` to the product space `X × Y`. -/
def binaryProductFunctor : DiffSp.{u} ⥤ DiffSp.{u} ⥤ DiffSp.{u} where
  obj X := {
    obj := fun Y ↦ of (X × Y)
    map := fun {Y Y'} f ↦ ⟨_,dsmooth_id.prod_map f.dsmooth⟩ }
  map {X Y} f := {
    app := fun Z ↦ ⟨_,f.dsmooth.prod_map dsmooth_id⟩
    naturality := fun {X' Y'} f' ↦ rfl }
  map_id := fun X ↦ rfl
  map_comp := fun {X Y Z} f g ↦ rfl

/-- The explicit products we defined are naturally isomorphic to the products coming from
  the `HasLimits` instance on DiffSp. This is needed because the `HasLimits`
  instance only stores proof that all limits exist, not the explicit constructions,
  so the products derived from it are picked with the axiom of choice. -/
noncomputable def binaryProductIsoProd : binaryProductFunctor.{u} ≅ (prod.functor) := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun _ ↦ ?_)
  · refine NatIso.ofComponents (fun Y ↦ ?_) (fun _ ↦ ?_)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2; apply Limits.prod.hom_ext <;> simp <;> rfl

/-- The one-point space as a cone. -/
def terminalCone : Cone (Functor.empty DiffSp.{u}) where
  pt := ⟨PUnit, ⊤⟩
  π := (Functor.uniqueFromEmpty _).hom

/-- `DiffSp.terminalCone` is actually limiting. -/
def terminalCodeIsLimit : IsLimit terminalCone where
  lift c := ⟨fun _ ↦ PUnit.unit, dsmooth_const⟩

end BinaryProducts

section Cartesian

instance : ChosenFiniteProducts DiffSp where
  product X Y := ⟨binaryProductCone X Y, binaryProductLimit X Y⟩
  terminal := ⟨terminalCone, terminalCodeIsLimit⟩

/-- `DiffSp` is cartesian-closed. -/
noncomputable instance cartesianClosed : CartesianClosed DiffSp.{u} where
  closed X := ⟨{
      obj := fun Y ↦ DiffSp.of (DSmoothMap X Y)
      map := fun f ↦ ⟨f.comp,DSmoothMap.dsmooth_comp.curry_right⟩
    }, by exact Adjunction.mkOfHomEquiv {
      homEquiv := fun Y Z ↦ (DDiffeomorph.prodComm.comp_right).toEquiv.trans
        (@DDiffeomorph.curry Y X Z _ _ _).toEquiv
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun _ _ ↦ rfl
    }⟩

end Cartesian

end DiffSp
