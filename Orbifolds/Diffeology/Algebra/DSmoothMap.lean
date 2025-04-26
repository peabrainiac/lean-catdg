import Orbifolds.Diffeology.Algebra.Module

/-!
# Algebraic structures on `DSmoothMap`

In this file put algebraic structure instance on the type `DSmoothMap X A` of
smooth maps from a diffeological space `X` to a diffeological algebraic structure `A`.
For example, `DSmoothMap X G` is a group under pointwise multiplication whenever `G` is a
diffeological group.

Adapted from `Mathlib.Topology.ContinuousMap.Algebra`.
-/

variable {X Y A : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace A]

namespace DSmoothMap

/-! ### `mul` and `add` -/

@[to_additive]
instance instMul [Mul A] [DSmoothMul A] : Mul (DSmoothMap X A) :=
  ⟨fun f g => ⟨f * g, f.dsmooth.mul g.dsmooth⟩⟩

@[to_additive (attr := norm_cast, simp)]
theorem coe_mul [Mul A] [DSmoothMul A] (f g : DSmoothMap X A) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
theorem mul_apply [Mul A] [DSmoothMul A] (f g : DSmoothMap X A) (x : X) : (f * g) x = f x * g x :=
  rfl

@[to_additive (attr := simp)]
theorem mul_comp [Mul A] [DSmoothMul A] (f₁ f₂ : DSmoothMap Y A) (g : DSmoothMap X Y) :
    (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
  rfl

/-! ### `one` and `zero` -/

@[to_additive]
instance [One A] : One (DSmoothMap X A) :=
  ⟨.const 1⟩

@[to_additive (attr := norm_cast, simp)]
theorem coe_one [One A] : ⇑(1 : DSmoothMap X A) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem one_apply [One A] (x : X) : (1 : DSmoothMap X A) x = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem one_comp [One A] (g : DSmoothMap X Y) : (1 : DSmoothMap Y A).comp g = 1 :=
  rfl

/-! ### `Nat.cast` -/

instance [NatCast A] : NatCast (DSmoothMap X A) :=
  ⟨fun n => .const n⟩

@[simp, norm_cast]
theorem coe_natCast [NatCast A] (n : ℕ) : ((n : DSmoothMap X A) : X → A) = n :=
  rfl

@[simp]
theorem natCast_apply [NatCast A] (n : ℕ) (x : X) : (n : DSmoothMap X A) x = n :=
  rfl

instance [IntCast A] : IntCast (DSmoothMap X A) :=
  ⟨fun n => .const n⟩

/-! ### `Int.cast` -/

@[simp, norm_cast]
theorem coe_intCast [IntCast A] (n : ℤ) : ((n : DSmoothMap X A) : X → A) = n :=
  rfl

@[simp]
theorem intCast_apply [IntCast A] (n : ℤ) (x : X) : (n : DSmoothMap X A) x = n :=
  rfl

/-! ### `nsmul` and `pow` -/

instance instNSMul [AddMonoid A] [DSmoothAdd A] : SMul ℕ (DSmoothMap X A) :=
  ⟨fun n f => ⟨n • ⇑f, f.dsmooth.nsmul n⟩⟩

@[to_additive existing]
instance instPow [Monoid A] [DSmoothMul A] : Pow (DSmoothMap X A) ℕ :=
  ⟨fun f n => ⟨(⇑f) ^ n, f.dsmooth.pow n⟩⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
theorem coe_pow [Monoid A] [DSmoothMul A] (f : DSmoothMap X A) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

@[to_additive (attr := norm_cast)]
theorem pow_apply [Monoid A] [DSmoothMul A] (f : DSmoothMap X A) (n : ℕ) (x : X) :
    (f ^ n) x = f x ^ n :=
  rfl

attribute [simp] coe_pow pow_apply

@[to_additive]
theorem pow_comp [Monoid A] [DSmoothMul A] (f : DSmoothMap Y A) (n : ℕ) (g : DSmoothMap X Y) :
    (f ^ n).comp g = f.comp g ^ n :=
  rfl

attribute [simp] pow_comp

/-! ### `inv` and `neg` -/

@[to_additive]
instance [Inv A] [DSmoothInv A] : Inv (DSmoothMap X A) where inv f := ⟨f⁻¹, f.dsmooth.inv⟩

@[to_additive (attr := simp)]
theorem coe_inv [Inv A] [DSmoothInv A] (f : DSmoothMap X A) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_apply [Inv A] [DSmoothInv A] (f :DSmoothMap X A) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_comp [Inv A] [DSmoothInv A] (f : DSmoothMap Y A) (g : DSmoothMap X Y) :
    f⁻¹.comp g = (f.comp g)⁻¹ :=
  rfl

/-! ### `div` and `sub` -/

@[to_additive]
instance [Div A] [DSmoothDiv A] : Div (DSmoothMap X A) where
  div f g := ⟨f / g, f.dsmooth.div' g.dsmooth⟩

@[to_additive (attr := norm_cast, simp)]
theorem coe_div [Div A] [DSmoothDiv A] (f g : DSmoothMap X A) : ⇑(f / g) = f / g :=
  rfl

@[to_additive (attr := simp)]
theorem div_apply [Div A] [DSmoothDiv A] (f g : DSmoothMap X A) (x : X) : (f / g) x = f x / g x :=
  rfl

@[to_additive (attr := simp)]
theorem div_comp [Div A] [DSmoothDiv A] (f g : DSmoothMap Y A) (h : DSmoothMap X Y) :
    (f / g).comp h = f.comp h / g.comp h :=
  rfl

/-! ### `zpow` and `zsmul` -/

instance instZSMul [AddGroup A] [DiffeologicalAddGroup A] : SMul ℤ (DSmoothMap X A) where
  smul z f := ⟨z • ⇑f, f.dsmooth.zsmul z⟩

@[to_additive existing]
instance instZPow [Group A] [DiffeologicalGroup A] : Pow (DSmoothMap X A) ℤ where
  pow f z := ⟨(⇑f) ^ z, f.dsmooth.zpow z⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
theorem coe_zpow [Group A] [DiffeologicalGroup A] (f : DSmoothMap X A) (z : ℤ) :
    ⇑(f ^ z) = (⇑f) ^ z :=
  rfl

@[to_additive]
theorem zpow_apply [Group A] [DiffeologicalGroup A] (f : DSmoothMap X A) (z : ℤ) (x : X) :
    (f ^ z) x = f x ^ z :=
  rfl

attribute [simp] coe_zpow zpow_apply

@[to_additive]
theorem zpow_comp [Group A] [DiffeologicalGroup A] (f : DSmoothMap Y A) (z : ℤ)
    (g : DSmoothMap X Y) : (f ^ z).comp g = f.comp g ^ z :=
  rfl

attribute [simp] zpow_comp

/-! ### Structure instances -/

@[to_additive]
instance [Semigroup A] [DSmoothMul A] : Semigroup (DSmoothMap X A) :=
  Function.Injective.semigroup _ coe_injective coe_mul

@[to_additive]
instance [CommSemigroup A] [DSmoothMul A] : CommSemigroup (DSmoothMap X A) :=
  Function.Injective.commSemigroup _ coe_injective coe_mul

@[to_additive]
instance [MulOneClass A] [DSmoothMul A] : MulOneClass (DSmoothMap X A) :=
  Function.Injective.mulOneClass _ coe_injective coe_one coe_mul

instance [MulZeroClass A] [DSmoothMul A] : MulZeroClass (DSmoothMap X A) :=
  Function.Injective.mulZeroClass _ coe_injective coe_zero coe_mul

instance [SemigroupWithZero A] [DSmoothMul A] : SemigroupWithZero (DSmoothMap X A) :=
  Function.Injective.semigroupWithZero _ coe_injective coe_zero coe_mul

@[to_additive]
instance [Monoid A] [DSmoothMul A] : Monoid (DSmoothMap X A) :=
  Function.Injective.monoid _ coe_injective coe_one coe_mul coe_pow

instance [MonoidWithZero A] [DSmoothMul A] : MonoidWithZero (DSmoothMap X A) :=
  Function.Injective.monoidWithZero _ coe_injective coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [CommMonoid A] [DSmoothMul A] : CommMonoid (DSmoothMap X A) :=
  Function.Injective.commMonoid _ coe_injective coe_one coe_mul coe_pow

instance [CommMonoidWithZero A] [DSmoothMul A] : CommMonoidWithZero (DSmoothMap X A) :=
  Function.Injective.commMonoidWithZero _ coe_injective coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [Group A] [DiffeologicalGroup A] : Group (DSmoothMap X A) :=
  Function.Injective.group _ coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance [CommGroup A] [DiffeologicalGroup A] : CommGroup (DSmoothMap X A) :=
  Function.Injective.commGroup _ coe_injective coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

instance [AddMonoidWithOne A] [DSmoothAdd A] : AddMonoidWithOne (DSmoothMap X A) :=
  Function.Injective.addMonoidWithOne _ coe_injective coe_zero coe_one coe_add coe_nsmul coe_natCast

instance [NonUnitalNonAssocRing A] [DiffeologicalRing A] : NonUnitalNonAssocRing (DSmoothMap X A) :=
  Function.Injective.nonUnitalNonAssocRing _ coe_injective coe_zero coe_add coe_mul coe_neg coe_sub
    coe_nsmul coe_zsmul

instance  [NonUnitalRing A] [DiffeologicalRing A] : NonUnitalRing (DSmoothMap X A) :=
  Function.Injective.nonUnitalRing _ coe_injective coe_zero coe_add coe_mul coe_neg coe_sub
    coe_nsmul coe_zsmul

instance  [NonAssocRing A] [DiffeologicalRing A] : NonAssocRing (DSmoothMap X A) :=
  Function.Injective.nonAssocRing _ coe_injective coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    coe_nsmul coe_zsmul coe_natCast coe_intCast

instance instRing [Ring A] [DiffeologicalRing A] : Ring (DSmoothMap X A) :=
  Function.Injective.ring _ coe_injective coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    coe_nsmul coe_zsmul coe_pow coe_natCast coe_intCast

instance  [NonUnitalCommRing A] [DiffeologicalRing A] : NonUnitalCommRing (DSmoothMap X A) :=
  Function.Injective.nonUnitalCommRing _ coe_injective coe_zero coe_add coe_mul coe_neg coe_sub
    coe_nsmul coe_zsmul

instance  [CommRing A] [DiffeologicalRing A] : CommRing (DSmoothMap X A) :=
  Function.Injective.commRing _ coe_injective coe_zero coe_one coe_add coe_mul coe_neg coe_sub
    coe_nsmul coe_zsmul coe_pow coe_natCast coe_intCast

/-- Coercion to a function as a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps)
  "Coercion to a function as an `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`." ]
def coeFnMonoidHom [Monoid A] [DSmoothMul A] : DSmoothMap X A →* X → A where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

/-- Coercion to a function as a `RingHom`. -/
@[simps!]
def coeFnRingHom [Ring A] [DiffeologicalRing A] : DSmoothMap X A →+* X → A :=
  { (coeFnMonoidHom : DSmoothMap X A →* _),
    (coeFnAddMonoidHom : DSmoothMap X A →+ _) with }

/-! ### Diffeological structure instances -/

@[to_additive]
instance [Mul A] [DSmoothMul A] : DSmoothMul (DSmoothMap X A) where
  dsmooth_mul _ _ hp := by
    refine DSmooth.mul ?_ ?_
    · exact dsmooth_eval.comp <|
        (dsmooth_fst.comp <| hp.dsmooth.comp dsmooth_fst).prod_mk dsmooth_snd
    · exact dsmooth_eval.comp <|
        (dsmooth_snd.comp <| hp.dsmooth.comp dsmooth_fst).prod_mk dsmooth_snd

@[to_additive]
instance [Inv A] [DSmoothInv A] : DSmoothInv (DSmoothMap X A) where
  dsmooth_inv _ _ hp :=
    dsmooth_inv.comp <| dsmooth_eval.comp <| (hp.dsmooth.comp dsmooth_fst).prod_mk dsmooth_snd

@[to_additive]
instance [Group A] [DiffeologicalGroup A] : DiffeologicalGroup (DSmoothMap X A) where

instance [NonUnitalNonAssocRing A] [DiffeologicalRing A] : DiffeologicalRing (DSmoothMap X A) where

/-! ### Modules and algebras -/

variable {R R' M : Type*} [DiffeologicalSpace R] [DiffeologicalSpace R'] [DiffeologicalSpace M]

/-- TODO: weaken this to `DSmoothConstSMul` once that is defined,
with no diffeology required on `R`. -/
@[to_additive]
instance instSMul [SMul R M] [DSmoothSMul R M] : SMul R (DSmoothMap X M) :=
  ⟨fun r f => ⟨r • ⇑f, dsmooth_const.smul f.dsmooth⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul [SMul R M] [DSmoothSMul R M] (c : R) (f : DSmoothMap X M) : ⇑(c • f) = c • ⇑f :=
  rfl

@[to_additive]
theorem smul_apply [SMul R M] [DSmoothSMul R M] (c : R) (f : DSmoothMap X M) (a : X) :
    (c • f) a = c • f a :=
  rfl

@[to_additive (attr := simp)]
theorem smul_comp [SMul R M] [DSmoothSMul R M] (r : R) (f : DSmoothMap Y M) (g : DSmoothMap X Y) :
    (r • f).comp g = r • f.comp g :=
  rfl

@[to_additive]
instance [SMul R M] [DSmoothSMul R M] : DSmoothSMul R (DSmoothMap X M) where
  dsmooth_smul n p hp := by
    refine DSmooth.smul ?_ ?_
    · exact dsmooth_fst.comp (hp.dsmooth.comp dsmooth_fst)
    · exact dsmooth_eval.comp <|
        (dsmooth_snd.comp <| hp.dsmooth.comp dsmooth_fst).prod_mk dsmooth_snd

@[to_additive]
instance [SMul R M] [DSmoothSMul R M] [SMul R' M] [DSmoothSMul R' M]
    [SMulCommClass R R' M] : SMulCommClass R R' (DSmoothMap X M) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance [SMul R M] [DSmoothSMul R M] [SMul R' M] [DSmoothSMul R' M] [SMul R R']
    [IsScalarTower R R' M] : IsScalarTower R R' (DSmoothMap X M) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance [SMul R M] [SMul Rᵐᵒᵖ M] [DSmoothSMul R M] [IsCentralScalar R M] :
    IsCentralScalar R (DSmoothMap X M) where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

instance [SMul R M] [DSmoothSMul R M] [Mul M] [DSmoothMul M] [IsScalarTower R M M] :
    IsScalarTower R (DSmoothMap X M) (DSmoothMap X M) where
  smul_assoc _ _ _ := ext fun _ => smul_mul_assoc ..

instance [SMul R M] [DSmoothSMul R M] [Mul M] [DSmoothMul M] [SMulCommClass R M M] :
    SMulCommClass R (DSmoothMap X M) (DSmoothMap X M) where
  smul_comm _ _ _ := ext fun _ => (mul_smul_comm ..).symm

instance [SMul R M] [DSmoothSMul R M] [Mul M] [DSmoothMul M] [SMulCommClass M R M] :
    SMulCommClass (DSmoothMap X M) R (DSmoothMap X M) where
  smul_comm _ _ _ := ext fun _ => smul_comm (_ : M) ..

instance [Monoid R] [MulAction R M] [DSmoothSMul R M] : MulAction R (DSmoothMap X M) :=
  Function.Injective.mulAction _ coe_injective coe_smul

instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [DSmoothAdd M]
    [DSmoothSMul R M] : DistribMulAction R (DSmoothMap X M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance module [Ring R] [AddCommMonoid M] [Module R M] [DSmoothAdd M] [DSmoothSMul R M] :
    Module R (DSmoothMap X M) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul

/-- Coercion to a function as a `LinearMap`. -/
@[simps]
def coeFnLinearMap [Ring R] [AddCommMonoid M] [Module R M] [DSmoothAdd M] [DSmoothSMul R M] :
    DSmoothMap X M →ₗ[R] X → M :=
  { (coeFnAddMonoidHom : DSmoothMap X M →+ _) with
    map_smul' := coe_smul }

omit [DiffeologicalSpace R] in
/-- Continuous constant functions as a `RingHom`. -/
def C [CommSemiring R] [Ring A] [Algebra R A] [DiffeologicalRing A] : R →+* (DSmoothMap X A) where
  toFun := fun c : R => ⟨fun _ : X => (algebraMap R A) c, dsmooth_const⟩
  map_one' := by ext _; exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext _; exact (algebraMap R A).map_mul _ _
  map_zero' := by ext _; exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext _; exact (algebraMap R A).map_add _ _

omit [DiffeologicalSpace R] in
@[simp]
theorem C_apply [CommSemiring R] [Ring A] [Algebra R A] [DiffeologicalRing A] (r : R) (x : X) :
    C r x = algebraMap R A r :=
  rfl

instance algebra [CommSemiring R] [Ring A] [Algebra R A] [DiffeologicalRing A] [DSmoothSMul R A] :
    Algebra R (DSmoothMap X A) where
  algebraMap := C
  commutes' c f := by ext x; exact Algebra.commutes' _ _
  smul_def' c f := by ext x; exact Algebra.smul_def' _ _

/-- In particular, for any diffeological space `X` the smooth real-valued functions on `X` form
an `ℝ`-algebra. -/
example : Algebra ℝ (DSmoothMap X ℝ) := inferInstance

/-- Similarly, smooth complex-valued functions form a complex algebra. -/
noncomputable example : Algebra ℂ (DSmoothMap X ℂ) := inferInstance
