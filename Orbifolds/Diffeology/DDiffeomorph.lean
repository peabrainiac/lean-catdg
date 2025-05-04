import Orbifolds.Diffeology.Constructions

open Function Set

open Topology

/-!
# Diffeomorphisms
Diffeomorphisms between diffeological spaces.
Mostly copied from `Mathlib.Geometry.Manifold.Diffeomorph`.
-/

structure DDiffeomorph (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y]
    extends X ≃ Y where
  protected dsmooth_toFun : DSmooth toFun
  protected dsmooth_invFun : DSmooth invFun

infixl:25 " ᵈ≃ " => DDiffeomorph

namespace DDiffeomorph

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

theorem toEquiv_injective : Injective (DDiffeomorph.toEquiv : X ᵈ≃ Y → X ≃ Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance : EquivLike (X ᵈ≃ Y) X Y where
  coe Φ := Φ.toEquiv
  inv Φ := Φ.toEquiv.symm
  left_inv Φ := Φ.left_inv
  right_inv Φ := Φ.right_inv
  coe_injective' _ _ h _ := toEquiv_injective (DFunLike.ext' h)

instance : CoeFun (X ᵈ≃ Y) fun _ ↦ X → Y := ⟨DFunLike.coe⟩

@[continuity]
protected theorem continuous (h : X ᵈ≃ Y) : Continuous[DTop,DTop] h := h.dsmooth_toFun.continuous

@[continuity]
protected theorem continuous' [TopologicalSpace X] [TopologicalSpace Y] [DTopCompatible X]
    [DTopCompatible Y] (h : X ᵈ≃ Y) : Continuous h := h.dsmooth_toFun.continuous'

protected theorem dsmooth (h : X ᵈ≃ Y) : DSmooth h := h.dsmooth_toFun

protected theorem induction (h : X ᵈ≃ Y) : Induction h :=
  h.left_inv.induction h.dsmooth_invFun h.dsmooth

protected theorem subduction (h : X ᵈ≃ Y) : Subduction h :=
  h.right_inv.subduction h.dsmooth h.dsmooth_invFun

@[simp]
theorem coe_toEquiv (h : X ᵈ≃ Y) : ⇑h.toEquiv = h := rfl

@[simp]
theorem toEquiv_inj {h h' : X ᵈ≃ Y} : h.toEquiv = h'.toEquiv ↔ h = h' :=
  toEquiv_injective.eq_iff

theorem coeFn_injective : Injective ((↑) : X ᵈ≃ Y → X → Y) :=
  DFunLike.coe_injective

-- TODO simp lemmas for this
def toDSmoothMap (d : X ᵈ≃ Y) : DSmoothMap X Y := ⟨d,d.dsmooth⟩

local instance : Coe (X ᵈ≃ Y) (DSmoothMap X Y) := ⟨DDiffeomorph.toDSmoothMap⟩

protected theorem bijective (h : X ᵈ≃ Y) : Function.Bijective h :=
  h.toEquiv.bijective

protected theorem injective (h : X ᵈ≃ Y) : Function.Injective h :=
  h.toEquiv.injective

protected theorem surjective (h : X ᵈ≃ Y) : Function.Surjective h :=
  h.toEquiv.surjective

@[ext]
theorem ext {h h' : X ᵈ≃ Y} (heq : ∀ x, h x = h' x) : h = h' :=
  coeFn_injective (funext heq)

/-- Identity map as a diffeomorphism. -/
protected def refl (X : Type*) [DiffeologicalSpace X] : X ᵈ≃ X where
  dsmooth_toFun := dsmooth_id
  dsmooth_invFun := dsmooth_id
  toEquiv := Equiv.refl X

@[simp]
theorem refl_toEquiv : (DDiffeomorph.refl X).toEquiv = Equiv.refl _ := rfl

@[simp]
theorem coe_refl : ⇑(DDiffeomorph.refl X) = id := rfl

/-- Composition of diffeomorphisms. -/
@[trans]
protected def trans (h₁ : X ᵈ≃ Y) (h₂ : Y ᵈ≃ Z) : X ᵈ≃ Z where
  dsmooth_toFun := h₂.dsmooth.comp h₁.dsmooth
  dsmooth_invFun := h₁.dsmooth_invFun.comp h₂.dsmooth_invFun
  toEquiv := h₁.toEquiv.trans h₂.toEquiv

@[simp]
theorem trans_refl (h : X ᵈ≃ Y) : h.trans (DDiffeomorph.refl Y) = h :=
  ext fun _ ↦ rfl

@[simp]
theorem refl_trans (h : X ᵈ≃ Y) : (DDiffeomorph.refl X).trans h = h :=
  ext fun _ ↦ rfl

@[simp]
theorem coe_trans (h₁ : X ᵈ≃ Y) (h₂ : Y ᵈ≃ Z) : ⇑(h₁.trans h₂) = h₂ ∘ h₁ :=
  rfl

/-- Inverse of a diffeomorphism. -/
@[symm]
protected def symm (h : X ᵈ≃ Y) : Y ᵈ≃ X where
  dsmooth_toFun := h.dsmooth_invFun
  dsmooth_invFun := h.dsmooth_toFun
  toEquiv := h.toEquiv.symm

@[simp]
theorem apply_symm_apply (h : X ᵈ≃ Y) (y : Y) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (h : X ᵈ≃ Y) (x : X) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

@[simp]
theorem symm_refl : (DDiffeomorph.refl X).symm = DDiffeomorph.refl X :=
  ext fun _ ↦rfl

@[simp]
theorem self_trans_symm (h : X ᵈ≃ Y) : h.trans h.symm = DDiffeomorph.refl X :=
  ext h.symm_apply_apply

@[simp]
theorem symm_trans_self (h : X ᵈ≃ Y) : h.symm.trans h = DDiffeomorph.refl Y :=
  ext h.apply_symm_apply

@[simp]
theorem symm_trans' (h₁ : X ᵈ≃ Y) (h₂ : Y ᵈ≃ Z) :
    (h₁.trans h₂).symm = h₂.symm.trans h₁.symm :=
  rfl

@[simp]
theorem symm_toEquiv (h : X ᵈ≃ Y) : h.symm.toEquiv = h.toEquiv.symm :=
  rfl

@[simp]
theorem toEquiv_coe_symm (h : X ᵈ≃ Y) : ⇑h.toEquiv.symm = h.symm :=
  rfl

theorem image_eq_preimage (h : X ᵈ≃ Y) (s : Set X) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage s

theorem symm_image_eq_preimage (h : X ᵈ≃ Y) (s : Set Y) : h.symm '' s = h ⁻¹' s :=
  h.symm.image_eq_preimage s

@[simp]
nonrec theorem range_comp {α : Type*} (h : X ᵈ≃ Y) (f : α → X) :
    range (h ∘ f) = h.symm ⁻¹' range f := by
  rw [range_comp, image_eq_preimage]

@[simp]
theorem image_symm_image (h : X ᵈ≃ Y) (s : Set Y) : h '' (h.symm '' s) = s :=
  h.toEquiv.image_symm_image s

@[simp]
theorem symm_image_image (h : X ᵈ≃ Y) (s : Set X) : h.symm '' (h '' s) = s :=
  h.toEquiv.symm_image_image s

/-- An induction is a diffeomorphism onto its image. -/
noncomputable def ofInduction {f : X → Y} (hf : Induction f) : X ᵈ≃ range f where
  toEquiv := Equiv.ofInjective f hf.1
  dsmooth_toFun := hf.dsmooth
  dsmooth_invFun := hf.dsmooth_iff.2 <| by simp [dsmooth_subtype_val]

/-- A diffeomorphism is a homeomorphism with respect to the D-topologies. -/
def toHomeomorph (h : X ᵈ≃ Y) : @Homeomorph X Y DTop DTop := by
  letI : TopologicalSpace X := DTop
  letI : TopologicalSpace Y := DTop
  exact ⟨h.toEquiv,h.continuous,h.symm.continuous⟩

@[simp]
theorem toHomeomorph_toEquiv (h : X ᵈ≃ Y) :
    @Homeomorph.toEquiv _ _ DTop DTop h.toHomeomorph = h.toEquiv :=
  rfl

@[simp]
theorem symm_toHomeomorph (h : X ᵈ≃ Y) :
    h.symm.toHomeomorph = @Homeomorph.symm _ _ DTop DTop h.toHomeomorph :=
  rfl

@[simp]
theorem coe_toHomeomorph (h : X ᵈ≃ Y) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
theorem coe_toHomeomorph_symm (h : X ᵈ≃ Y) :
    ⇑(@Homeomorph.symm _ _ DTop DTop h.toHomeomorph) = h.symm :=
  rfl

/-- A diffeomorphism between spaces that are equipped with the D-topologies is also
  a homeoomorphism. -/
def toHomeomorph' [TopologicalSpace X] [TopologicalSpace Y] [DTopCompatible X]
    [DTopCompatible Y] (h : X ᵈ≃ Y) : X ≃ₜ Y := by
  exact ⟨h.toEquiv,h.dsmooth.continuous',h.symm.dsmooth.continuous'⟩

@[simp]
theorem toHomeomorph_toEquiv' [TopologicalSpace X] [TopologicalSpace Y] [DTopCompatible X]
    [DTopCompatible Y] (h : X ᵈ≃ Y) : h.toHomeomorph'.toEquiv = h.toEquiv :=
  rfl

@[simp]
theorem symm_toHomeomorph' [TopologicalSpace X] [TopologicalSpace Y] [DTopCompatible X]
    [DTopCompatible Y] (h : X ᵈ≃ Y) : h.symm.toHomeomorph' = h.toHomeomorph'.symm :=
  rfl

@[simp]
theorem coe_toHomeomorph' [TopologicalSpace X] [TopologicalSpace Y] [DTopCompatible X]
    [DTopCompatible Y] (h : X ᵈ≃ Y) : ⇑h.toHomeomorph' = h :=
  rfl

@[simp]
theorem coe_toHomeomorph_symm' [TopologicalSpace X] [TopologicalSpace Y] [DTopCompatible X]
    [DTopCompatible Y] (h : X ᵈ≃ Y) : ⇑(h.toHomeomorph'.symm) = h.symm :=
  rfl

@[simp]
theorem dsmooth_comp_ddiffeomorph_iff (h : X ᵈ≃ Y) {f : Y → Z} :
    DSmooth (f ∘ h) ↔ DSmooth f := by
  refine ⟨fun h' ↦ ?_, fun hf ↦ hf.comp h.dsmooth⟩
  rw [←comp_id f, ←coe_refl, ←symm_trans_self h, coe_trans, ←comp_assoc]
  exact h'.comp h.symm.dsmooth

@[simp]
theorem dsmooth_ddiffeomorph_comp_iff (h : X ᵈ≃ Y) {f : Z → X} :
    DSmooth (h ∘ f) ↔ DSmooth f := by
  refine ⟨fun h' ↦ ?_, fun hf ↦ h.dsmooth.comp hf⟩
  rw [←id_comp f, ←coe_refl, ←self_trans_symm h, coe_trans, comp_assoc]
  exact h.symm.dsmooth.comp h'

section Constructions

open PartialHomeomorph in
/-- Inner product spaces are diffeomorphic to open balls in them. -/
noncomputable def univBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [DiffeologicalSpace E] [ContDiffCompatible E] (x : E) {r : ℝ} (hr : r > 0) :
     E ᵈ≃ (Metric.ball x r) where
  toEquiv := by
    rw [←unitBallBall_target x r hr]
    exact (Equiv.Set.univ _).symm.trans
      (univUnitBall.toHomeomorphSourceTarget.trans
        (unitBallBall x r hr).toHomeomorphSourceTarget).toEquiv
  dsmooth_toFun := by
    exact (contDiff_unitBallBall hr).dsmooth.comp contDiff_univUnitBall.dsmooth
  dsmooth_invFun := by
    have h₁ : DSmooth (univUnitBall (E := E)).toHomeomorphSourceTarget.symm :=
      ContDiffOn.dsmooth_restrict contDiffOn_univUnitBall_symm
    have h₂ : DSmooth (unitBallBall x r hr).toHomeomorphSourceTarget.symm :=
      (contDiff_unitBallBall_symm hr).dsmooth.restrict (unitBallBall x r hr).symm_mapsTo
    exact dsmooth_subtype_val.comp (h₁.comp h₂)


/-- `Set.univ X` is diffeomorphic to `X`. -/
@[simps! -fullyApplied]
def Set.univ (X : Type*) [DiffeologicalSpace X] : (univ : Set X) ᵈ≃ X where
  toEquiv := Equiv.Set.univ X
  dsmooth_toFun := dsmooth_subtype_val
  dsmooth_invFun := dsmooth_id.subtype_mk _

def Set.nested {u : Set X} (v : Set u) : v ᵈ≃ ((↑) '' v : Set X) where
  toEquiv := {
    toFun := (v.mapsTo_image (@Subtype.val X u)).restrict
    invFun := fun x ↦ ⟨⟨↑x,by have ⟨y,hy⟩ := x.2; exact hy.2 ▸ y.2⟩,
      by have ⟨y,hy⟩ := x.2; exact (show y = ⟨↑x,_⟩ by ext; exact hy.2) ▸ hy.1⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
  }
  dsmooth_toFun := dsmooth_subtype_val.restrict _
  dsmooth_invFun := by exact (dsmooth_subtype_val.subtype_mk _).subtype_mk _

protected def restrict (d : X ᵈ≃ Y) (u : Set X) : u ᵈ≃ (d.symm ⁻¹' u) where
  toEquiv := {
    toFun := (d.image_eq_preimage _ ▸ Set.mapsTo_image d u).restrict
    invFun := u.restrictPreimage d.symm
    left_inv := fun x ↦ by ext; exact d.left_inv x.1
    right_inv := fun y ↦ by ext; exact d.right_inv y.1
  }
  dsmooth_toFun := d.dsmooth_toFun.restrict _
  dsmooth_invFun := d.dsmooth_invFun.restrict _

protected def restrictPreimage (d : X ᵈ≃ Y) (u : Set Y) : (d ⁻¹' u) ᵈ≃ u where
  toEquiv := {
    toFun := u.restrictPreimage d
    invFun := (d.symm.image_eq_preimage _ ▸ Set.mapsTo_image d.symm u).restrict
    left_inv := fun x ↦ by ext; exact d.left_inv x.1
    right_inv := fun y ↦ by ext; exact d.right_inv y.1
  }
  dsmooth_toFun := d.dsmooth_toFun.restrict _
  dsmooth_invFun := d.dsmooth_invFun.restrict _

/-- The quotient of `X` by the identity relation is diffeomorphic to `X`. -/
@[simps! -fullyApplied]
def quotient_bot (X : Type*) [DiffeologicalSpace X] : @Quotient X ⊥ ᵈ≃ X where
  toEquiv := {
    toFun := Quotient.lift id fun a b ↦ id
    invFun := @Quotient.mk' X ⊥
    left_inv := fun x ↦ by
      rw [←show @Quotient.mk' X ⊥ _ = x from @Quotient.out_eq X ⊥ x,@Quotient.eq']; rfl
    right_inv := fun _ ↦ rfl
  }
  dsmooth_toFun := dsmooth_id.quotient_lift _
  dsmooth_invFun := dsmooth_quotient_mk'

-- TODO!

def prodComm : X × Y ᵈ≃ Y × X where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  dsmooth_toFun := dsmooth_swap
  dsmooth_invFun := dsmooth_swap

/-- The currying diffeomorphism `DSmoothMap (X × Y) Z ᵈ≃ DSmoothMap X (DSmoothMap Y Z)`. -/
def curry : DSmoothMap (X × Y) Z ᵈ≃ DSmoothMap X (DSmoothMap Y Z) where
  toFun := DSmoothMap.curry
  invFun := DSmoothMap.uncurry
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  dsmooth_toFun := DSmoothMap.dsmooth_curry
  dsmooth_invFun := DSmoothMap.dsmooth_uncurry

/-- Postcomposition with `d : Y ᵈ≃ Z` as a diffeomorphism `DSmoothMap X Y ᵈ≃ DSmoothMap X Z`. -/
def comp_left (d : Y ᵈ≃ Z) : DSmoothMap X Y ᵈ≃ DSmoothMap X Z where
  toFun := fun f ↦ d.toDSmoothMap.comp f
  invFun := fun f ↦ d.symm.toDSmoothMap.comp f
  left_inv := fun f ↦ by ext x; exact symm_apply_apply d (f x)
  right_inv := fun f ↦ by ext x; exact apply_symm_apply d (f x)
  dsmooth_toFun := DSmoothMap.dsmooth_comp.curry_right
  dsmooth_invFun := DSmoothMap.dsmooth_comp.curry_right

/-- Precomposition with `d : X ᵈ≃ Y` as a diffeomorphism `DSmoothMap Y Z ᵈ≃ DSmoothMap X Z`. -/
def comp_right (d : X ᵈ≃ Y) : DSmoothMap Y Z ᵈ≃ DSmoothMap X Z where
  toFun := fun f ↦ f.comp d
  invFun := fun f ↦ f.comp d.symm
  left_inv := fun f ↦ by ext x; exact congrArg f <| apply_symm_apply d x
  right_inv := fun f ↦ by ext x; exact congrArg f <| symm_apply_apply d x
  dsmooth_toFun := DSmoothMap.dsmooth_comp.curry_left
  dsmooth_invFun := DSmoothMap.dsmooth_comp.curry_left

end Constructions

end DDiffeomorph

namespace ContinuousLinearEquiv

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DiffeologicalSpace E]
  [ContDiffCompatible E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [DiffeologicalSpace E']
  [ContDiffCompatible E'] (e : E ≃L[ℝ] E')

/-- A continuous linear equivalence between (for now just finite-dimensional) normed spaces
is a diffeomorphism. -/
def toDDiffeomorph : E ᵈ≃ E' where
  dsmooth_toFun := e.contDiff.dsmooth
  dsmooth_invFun := e.symm.contDiff.dsmooth
  toEquiv := e.toLinearEquiv.toEquiv

@[simp]
theorem coe_toDDiffeomorph : ⇑e.toDDiffeomorph = e := rfl

@[simp]
theorem symm_toDDiffeomorph : e.symm.toDDiffeomorph = (e.toDDiffeomorph).symm := rfl

@[simp]
theorem coe_toDDiffeomorph_symm : ⇑(e.toDDiffeomorph).symm = e.symm :=
  rfl

end ContinuousLinearEquiv
