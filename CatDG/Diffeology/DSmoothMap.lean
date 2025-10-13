import CatDG.Diffeology.Basic

/-!
# Bundled smooth maps

Defines the type `DSmoothMap X Y` of smooth maps between diffeological spaces.

This file contains only very basic API; more advanced constructions are done in
`CatDG.Diffeology.Constructions`.

Adapted from `Mathlib.Topology.ContinuousMap.Def` and `Mathlib.Topology.ContinuousMap.Basic`.

## TODO

* move this into a folder together with `CatDG.Diffeology.Algebra.DSmoothMap` and the relevant
  constructions from `CatDG.Diffeology.Constructions`.
* maybe introduce a notation like `C∞(X, Y)` or `X →C∞ Y` for `DSmoothMap X Y`?
-/

universe u v

/-- The type of bundled smooth maps between diffeological spaces `X` and `Y`. -/
structure DSmoothMap (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] where
  /-- The map `X → Y`. -/
  protected toFun : X → Y
  /-- The map `X → Y` is smooth. -/
  protected dsmooth : DSmooth toFun := by fun_prop

/-- `DSmoothMapClass F X Y` states that `F` is a type of smooth maps `X → Y`. -/
class DSmoothMapClass (F : Type*) (X Y : outParam Type*)
    [DiffeologicalSpace X] [DiffeologicalSpace Y] [FunLike F X Y] : Prop where
  /-- Smoothness. -/
  map_dsmooth (f : F) : DSmooth f

export DSmoothMapClass (map_dsmooth)

attribute [fun_prop] map_dsmooth

namespace DSmoothMapClass

variable {F X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [FunLike F X Y]
  [DSmoothMapClass F X Y]

/-- Coerce a bundled morphism with a `DSmoothMapClass` instance to a `DSmoothMap`. -/
@[coe] def toDSmoothMap (f : F) : DSmoothMap X Y := ⟨f, map_dsmooth f⟩

instance : CoeTC F (DSmoothMap X Y) := ⟨toDSmoothMap⟩

end DSmoothMapClass

namespace DSmoothMap

variable {X Y Z W : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]
  [DiffeologicalSpace W]

instance instFunLike : FunLike (DSmoothMap X Y) X Y where
  coe := DSmoothMap.toFun
  coe_injective' f g _ := by cases f; cases g; congr

instance instDSmoothMapClass : DSmoothMapClass (DSmoothMap X Y) X Y where
  map_dsmooth := DSmoothMap.dsmooth


@[simp]
lemma toFun_eq_coe {f : DSmoothMap X Y} : f.toFun = (f : X → Y) :=
  rfl

instance : CanLift (X → Y) (DSmoothMap X Y) DFunLike.coe DSmooth := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- See note [custom simps projection]. -/
def Simps.apply (f : (DSmoothMap X Y)) : X → Y := f

initialize_simps_projections DSmoothMap (toFun → apply)

@[simp]
protected lemma coe_coe {F : Type*} [FunLike F X Y] [DSmoothMapClass F X Y] (f : F) :
    ⇑(f : DSmoothMap X Y) = f :=
  rfl

protected lemma coe_apply {F : Type*} [FunLike F X Y] [DSmoothMapClass F X Y] (f : F) (x : X) :
    (f : DSmoothMap X Y) x = f x :=
  rfl

@[ext]
lemma ext {f g : DSmoothMap X Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

lemma coe_injective : Function.Injective (DFunLike.coe : DSmoothMap X Y → (X → Y)) :=
  DFunLike.coe_injective

@[simp]
lemma coe_mk (f : X → Y) (hf : DSmooth f) : ⇑(⟨f, hf⟩ : DSmoothMap X Y) = f :=
  rfl


variable (X) in
/-- The identity as a smooth map. -/
protected def id : DSmoothMap X X where
  toFun := id

variable (X) in
@[simp, norm_cast]
lemma coe_id : ⇑(DSmoothMap.id X) = id :=
  rfl

@[simp]
lemma id_apply (x : X) : DSmoothMap.id X x = x :=
  rfl

variable (X) in
/-- The constant map as a continuous map. -/
def const (y : Y) : DSmoothMap X Y where
  toFun := fun _ : X ↦ y

variable (X) in
@[simp]
lemma coe_const {y : Y} : ⇑(const X y) = Function.const X y :=
  rfl

@[simp]
lemma const_apply (y : Y) (x : X) : const X y x = y :=
  rfl

instance [Inhabited Y] : Inhabited (DSmoothMap X Y) :=
  ⟨const X default⟩

instance [Unique Y] : Unique (DSmoothMap X Y) where
  uniq _ := ext fun _ ↦ Unique.eq_default _

instance [Nonempty X] [Nontrivial Y] : Nontrivial (DSmoothMap X Y) :=
  ⟨let ⟨y₁, y₂, hy⟩ := exists_pair_ne Y
  ⟨const _ y₁, const _ y₂, fun h ↦ hy <| DFunLike.congr_fun h <| Classical.arbitrary X⟩⟩

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : DSmoothMap Y Z) (g : DSmoothMap X Y) : DSmoothMap X Z where
  toFun := f ∘ g

@[simp]
lemma coe_comp (f : DSmoothMap Y Z) (g : DSmoothMap X Y) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
lemma comp_apply (f : DSmoothMap Y Z) (g : DSmoothMap X Y) (x : X) : comp f g x = f (g x) :=
  rfl

@[simp]
lemma comp_assoc (f : DSmoothMap Z W) (g : DSmoothMap Y Z) (h : DSmoothMap X Y) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
lemma id_comp (f : DSmoothMap X Y) : (DSmoothMap.id _).comp f = f :=
  ext fun _ ↦ rfl

@[simp]
lemma comp_id (f : DSmoothMap X Y) : f.comp (DSmoothMap.id _) = f :=
  ext fun _ ↦ rfl

@[simp]
lemma const_comp (z : Z) (f : DSmoothMap X Y) : (const Y z).comp f = const X z :=
  ext fun _ ↦ rfl

@[simp]
lemma comp_const (f : DSmoothMap Y Z) (y : Y) : f.comp (const X y) = const X (f y) :=
  ext fun _ ↦ rfl

@[simp]
lemma cancel_right {f₁ f₂ : DSmoothMap Y Z} {g : DSmoothMap X Y} (hg : Function.Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (DSmoothMap.comp · g)⟩

@[simp]
lemma cancel_left {f : DSmoothMap Y Z} {g₁ g₂ : DSmoothMap X Y} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h ↦ ext fun a ↦ hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end DSmoothMap
