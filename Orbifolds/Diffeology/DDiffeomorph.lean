import Orbifolds.Diffeology.Basic

open Function Set

open Topology

/-!
# Diffeomorphisms
Diffeomorphisms between diffeological spaces.
Mostly copied from `Mathlib.Geometry.Manifold.Diffeomorph`.
-/

set_option autoImplicit false

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

@[continuity]
protected theorem continuous (h : X ᵈ≃ Y) : Continuous[DTop,DTop] h := h.dsmooth_toFun.continuous

protected theorem dsmooth (h : X ᵈ≃ Y) : DSmooth h := h.dsmooth_toFun

@[simp]
theorem coe_toEquiv (h : X ᵈ≃ Y) : ⇑h.toEquiv = h := rfl

@[simp]
theorem toEquiv_inj {h h' : X ᵈ≃ Y} : h.toEquiv = h'.toEquiv ↔ h = h' :=
  toEquiv_injective.eq_iff

theorem coeFn_injective : Injective ((↑) : X ᵈ≃ Y → X → Y) :=
  DFunLike.coe_injective

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
  ext fun _ => rfl

@[simp]
theorem refl_trans (h : X ᵈ≃ Y) : (DDiffeomorph.refl X).trans h = h :=
  ext fun _ => rfl

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
  ext fun _ => rfl

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

@[simp]
theorem dsmooth_comp_ddiffeomorph_iff (h : X ᵈ≃ Y) {f : Y → Z} :
    DSmooth (f ∘ h) ↔ DSmooth f := by
  refine' ⟨fun h' => _, fun hf => hf.comp h.dsmooth⟩
  rw [←comp_id f, ←coe_refl, ←symm_trans_self h, coe_trans, ←comp.assoc]
  exact h'.comp h.symm.dsmooth

@[simp]
theorem dsmooth_ddiffeomorph_comp_iff (h : X ᵈ≃ Y) {f : Z → X} :
    DSmooth (h ∘ f) ↔ DSmooth f := by
  refine' ⟨fun h' => _, fun hf => h.dsmooth.comp hf⟩
  rw [←id_comp f, ←coe_refl, ←self_trans_symm h, coe_trans, comp.assoc]
  exact h.symm.dsmooth.comp h'

section Constructions

-- TODO!

end Constructions

end DDiffeomorph

namespace ContinuousLinearEquiv

variable (E E' : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] (e : E ≃L[ℝ] E')

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
