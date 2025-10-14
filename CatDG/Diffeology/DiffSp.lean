import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Topology.Category.DeltaGenerated
import Mathlib.Topology.Category.TopCat.Basic
import CatDG.Diffeology.DDiffeomorph

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

section Basic

/-- The category of diffeological spaces. -/
structure DiffSp where
  private mk ::
  carrier : Type u
  [str : DiffeologicalSpace carrier]

attribute [instance] DiffSp.str

initialize_simps_projections DiffSp (-str)

namespace DiffSp

instance : CoeSort DiffSp (Type u) :=
  ⟨DiffSp.carrier⟩

attribute [coe] DiffSp.carrier

/-- The object in `DiffSp` associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `DiffSp`. -/
abbrev of (X : Type u) [DiffeologicalSpace X] : DiffSp :=
  ⟨X⟩

lemma coe_of (X : Type u) [DiffeologicalSpace X] : (of X : Type u) = X :=
  rfl

lemma of_carrier (X : DiffSp.{u}) : of X = X := rfl

variable {X} in
/-- The type of morphisms in `DiffSp`. -/
@[ext]
structure Hom (X Y : DiffSp.{u}) where
  private mk ::
  /-- The underlying `DSmoothMap`. -/
  hom' : DSmoothMap X Y

instance : Category DiffSp where
  Hom X Y := Hom X Y
  id X := ⟨DSmoothMap.id _⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} DiffSp (fun X Y => DSmoothMap X Y) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `DiffSp` back into a `DSmoothMap`. -/
abbrev Hom.hom {X Y : DiffSp.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := DiffSp) f

/-- Typecheck a `DSmoothMap` as a morphism in `DiffSp`. -/
abbrev ofHom {X Y : Type u} [DiffeologicalSpace X] [DiffeologicalSpace Y] (f : DSmoothMap X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := DiffSp) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : DiffSp) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
lemma hom_id (X : DiffSp) : (𝟙 X : X ⟶ X).hom = DSmoothMap.id X := rfl

@[simp]
lemma id_app (X : DiffSp) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

@[simp]
lemma coe_id (X : DiffSp) : (𝟙 X : X → X) = id := rfl

@[simp]
lemma hom_comp {X Y Z : DiffSp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
lemma comp_app {X Y Z : DiffSp} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

@[simp]
lemma coe_comp {X Y Z : DiffSp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl

@[ext]
lemma hom_ext {X Y : DiffSp} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[ext]
lemma ext {X Y : DiffSp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
lemma hom_ofHom {X Y : Type u} [DiffeologicalSpace X] [DiffeologicalSpace Y] (f : DSmoothMap X Y) :
  (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {X Y : DiffSp} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [DiffeologicalSpace X] : ofHom (DSmoothMap.id X) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [DiffeologicalSpace X] [DiffeologicalSpace Y]
    [DiffeologicalSpace Z] (f : DSmoothMap X Y) (g : DSmoothMap Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [DiffeologicalSpace X] [DiffeologicalSpace Y]
    (f : DSmoothMap X Y) (x : X) :
    (ofHom f) x = f x := rfl

lemma hom_inv_id_apply {X Y : DiffSp} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x := by
  simp

lemma inv_hom_id_apply {X Y : DiffSp} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y := by
  simp

@[simps!]
def homEquivDSmoothMap {X Y : DiffSp} : (X ⟶ Y) ≃ DSmoothMap X Y where
  toFun := Hom.hom
  invFun := ofHom
  left_inv _ := rfl
  right_inv _ := rfl

/--
Replace a function coercion for a morphism `DiffSp.of X ⟶ DiffSp.of Y` with the definitionally
equal function coercion for a smooth map `DSmoothMap X Y`.
-/
@[simp] theorem coe_of_of {X Y : Type u} [DiffeologicalSpace X] [DiffeologicalSpace Y]
    {f : DSmoothMap X Y} {x} :
    @DFunLike.coe (DiffSp.of X ⟶ DiffSp.of Y) ((CategoryTheory.forget DiffSp).obj (DiffSp.of X))
      (fun _ ↦ (CategoryTheory.forget DiffSp).obj (DiffSp.of Y)) HasForget.instFunLike
      (ofHom f) x =
    @DFunLike.coe (DSmoothMap X Y) X
      (fun _ ↦ Y) _
      f x :=
  rfl

instance inhabited : Inhabited DiffSp :=
  ⟨@of Empty ⊥⟩

/-- The functor equipping each type with the discrete diffeology. -/
def discrete : Type u ⥤ DiffSp.{u} where
  obj X := @of X ⊥
  map f := @ofHom _ _ (_) (_) <| @DSmoothMap.mk _ _ (_) (_) f dsmooth_bot

/-- The functor equipping each type with the indiscrete diffeology. -/
def indiscrete : Type u ⥤ DiffSp.{u} where
  obj X := @of X ⊤
  map f := @ofHom _ _ (_) (_) <| @DSmoothMap.mk _ _ (_) (_) f dsmooth_top

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
  obj X := @TopCat.of X DTop
  map f := @TopCat.ofHom _ _ (_) (_) <| @ContinuousMap.mk _ _ (_) (_) f f.hom.dsmooth.continuous

/-- The functor sending each diffeological space to its D-topology, as a delta-generated
space. -/
def diffToDeltaGenerated : DiffSp.{u} ⥤ DeltaGenerated.{u} where
  obj X := ⟨@TopCat.of X DTop,inferInstance⟩
  map f := @TopCat.ofHom _ _ (_) (_) <| @ContinuousMap.mk _ _ (_) (_) f f.hom.dsmooth.continuous

/-- The functor equipping each topological space with the continuous diffeology. -/
def topToDiff : TopCat.{u} ⥤ DiffSp.{u} where
  obj X := of (withContinuousDiffeology X)
  map f := @ofHom _ _ (_) (_) <| @DSmoothMap.mk _ _ (_) (_) f f.hom.continuous.dsmooth

/-- The functor equipping each delta-generated space with the continuous diffeology. -/
def deltaGeneratedToDiff : DeltaGenerated.{u} ⥤ DiffSp.{u} where
  obj X := of (withContinuousDiffeology X)
  map f := @ofHom _ _ (_) (_) <| @DSmoothMap.mk _ _ (_) (_) f f.hom.continuous.dsmooth

/-- Adjunction between the D-topology and continuous diffeology as functors between
`DiffSp` and `TopCat`. -/
def dTopAdj : dTop ⊣ topToDiff :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun X ↦ @ofHom _ _ (_) (_) <| @DSmoothMap.mk _ _ (_) (_) id
        dsmooth_id.continuous.dsmooth' }
    counit := {
      app := fun X ↦ @TopCat.ofHom _ _ (_) (_) <| @ContinuousMap.mk _ _ (_) (_) id <|
        continuous_iff_coinduced_le.mpr deltaGenerated_le } }

/-- Adjunction between the D-topology and continuous diffeology as functors between
`DiffSp` and `DeltaGenerated`. -/
def dTopAdj' : diffToDeltaGenerated ⊣ deltaGeneratedToDiff :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app := fun X ↦ @ofHom _ _ (_) (_) <| @DSmoothMap.mk _ _ (_) (_) id
        dsmooth_id.continuous.dsmooth' }
    counit := {
      app := fun X ↦ @TopCat.ofHom _ _ (_) (_) <| @ContinuousMap.mk _ _ (_) (_) id <|
        continuous_iff_coinduced_le.mpr dTop_continuousDiffeology_eq_self.le } }

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
        exact hom_ext <| DSmoothMap.ext fun a ↦ (a.2 f).symm }

/-- `DiffSp.limitCone F` is actually a limit cone for the given `F : J ⥤ DiffSp`. -/
def limitConeIsLimit (F : J ⥤ DiffSp.{max v u}) : IsLimit (limitCone.{u,v} F) where
  lift S :=
    ⟨fun x ↦ ⟨fun j ↦ S.π.app _ x, fun f ↦ by dsimp; exact S.w f ▸ rfl⟩,
    DSmooth.subtype_mk (dsmooth_pi fun j ↦ (S.π.app j).hom.dsmooth) fun x i j f ↦ by
      dsimp; exact S.w f ▸ rfl⟩
  fac S j := by dsimp [limitCone]; rfl
  uniq S m h := hom_ext <| DSmoothMap.ext fun a ↦ Subtype.ext <| by simp_rw [← h]; rfl

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

variable {F : J ⥤ DiffSp.{u}} (c : Cocone (F ⋙ forget))

/-- Given a functor `F : J ⥤ DiffSp` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is the type `c.pt`
with the infimum of the diffeologies that are coinduced by the maps `c.ι.app j`. -/
def coconePtOfCoconeForget : Type _ := c.pt

instance diffeologicalSpaceCoconePtOfCoconeForget : DiffeologicalSpace (coconePtOfCoconeForget c) :=
  (⨆ j, (F.obj j).str.coinduced (c.ι.app j))

/-- Given a functor `F : J ⥤ DiffSp` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is a cocone for `F` whose point is
`c.pt` with the infimum of the coinduced diffeologies by the maps `c.ι.app j`. -/
@[simps pt ι_app]
def coconeOfCoconeForget : Cocone F where
  pt := of (coconePtOfCoconeForget c)
  ι :=
    { app j := ofHom (DSmoothMap.mk (c.ι.app j) (by
        rw [dsmooth_iff_coinduced_le]
        exact le_iSup (fun j ↦ (F.obj j).str.coinduced (c.ι.app j)) j))
      naturality j j' φ := by
        ext; apply congr_fun (c.ι.naturality φ) }

/-- Given a functor `F : J ⥤ DiffSp` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, the colimit of `F` is `c.pt` equipped
with the supremum of the coinduced diffeologies by the maps `c.ι.app j`. -/
def isColimitCoconeOfForget (c : Cocone (F ⋙ forget)) (hc : IsColimit c) :
    IsColimit (coconeOfCoconeForget c) := by
  refine IsColimit.ofFaithful forget (ht := hc)
    (fun s ↦ ofHom (DSmoothMap.mk (hc.desc ((forget).mapCocone s)) ?_)) (fun _ ↦ rfl)
  rw [dsmooth_iff_le_induced]
  dsimp [diffeologicalSpaceCoconePtOfCoconeForget]
  rw [iSup_le_iff]
  intro j
  rw [DiffeologicalSpace.coinduced_le_iff_le_induced, DiffeologicalSpace.induced_compose]
  convert dsmooth_iff_le_induced.1 (s.ι.app j).hom.dsmooth
  exact hc.fac ((forget).mapCocone s) j

instance hasColimitsOfSize : HasColimitsOfSize.{v,v} DiffSp.{max v u} where
  has_colimits_of_shape _ := ⟨fun _ ↦ HasColimit.mk
    ⟨_, isColimitCoconeOfForget _ (colimit.isColimit _)⟩⟩

/-- `DiffSp` has all colimits, i.e. it is cocomplete. -/
instance hasColimits : HasColimits DiffSp.{u} :=
  hasColimitsOfSize.{u,u}

noncomputable instance forgetPreservesColimitsOfSize :
    PreservesColimitsOfSize.{v,v} (forget : DiffSp.{max v u} ⥤ _) :=
  ⟨⟨fun {_} ↦ preservesColimit_of_preserves_colimit_cocone
    (isColimitCoconeOfForget _ (colimit.isColimit _)) (colimit.isColimit _)⟩⟩

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
  lift (s : BinaryFan X Y) := ⟨_,s.fst.hom.dsmooth.prod_mk s.snd.hom.dsmooth⟩
  fac _ j := Discrete.recOn j fun j ↦ by cases j <;> rfl
  uniq s f w := hom_ext <| DSmoothMap.ext fun x ↦ Prod.ext
    (congrFun (congrArg DSmoothMap.toFun <| congrArg Hom.hom (w ⟨left⟩)) x)
    (congrFun (congrArg DSmoothMap.toFun <| congrArg Hom.hom (w ⟨right⟩)) x)

/-- The functor taking `X`, `Y` to the product space `X × Y`. -/
def binaryProductFunctor : DiffSp.{u} ⥤ DiffSp.{u} ⥤ DiffSp.{u} where
  obj X := {
    obj := fun Y ↦ of (X × Y)
    map := fun {Y Y'} f ↦ ⟨_,dsmooth_id.prod_map f.hom.dsmooth⟩ }
  map {X Y} f := {
    app := fun Z ↦ ⟨_,f.hom.dsmooth.prod_map dsmooth_id⟩
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
  pt := @of PUnit ⊤
  π := (Functor.uniqueFromEmpty _).hom

/-- `DiffSp.terminalCone` is actually limiting. -/
def terminalCodeIsLimit : IsLimit terminalCone where
  lift c := ⟨fun _ ↦ PUnit.unit, dsmooth_const⟩

end BinaryProducts

section Cartesian

instance : CartesianMonoidalCategory DiffSp :=
  .ofChosenFiniteProducts ⟨terminalCone, terminalCodeIsLimit⟩
    fun X Y ↦ ⟨binaryProductCone X Y, binaryProductLimit X Y⟩

/-- `DiffSp` is cartesian-closed. -/
noncomputable instance cartesianClosed : CartesianClosed DiffSp.{u} where
  closed X := ⟨{
      obj := fun Y ↦ DiffSp.of (DSmoothMap X Y)
      map := fun f ↦ ⟨f.hom.comp,DSmoothMap.dsmooth_comp.curry_right⟩
    }, by exact Adjunction.mkOfHomEquiv {
      homEquiv := fun Y Z ↦ by
        refine homEquivDSmoothMap.trans (Equiv.trans ?_ homEquivDSmoothMap.symm)
        exact (DDiffeomorph.prodComm.comp_right).toEquiv.trans
          (@DDiffeomorph.curry Y X Z _ _ _).toEquiv
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun _ _ ↦ rfl
    }⟩

end Cartesian

end DiffSp
