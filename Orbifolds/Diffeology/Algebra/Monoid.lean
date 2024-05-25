import Orbifolds.Diffeology.Algebra.MulAction

set_option autoImplicit false

/-!
# Smooth  monoids
Adapted from `Mathlib.Topology.Algebra.Monoid`.
For now this just contains a few basic definitions and lemmas, used to build up the theory of
diffeological groups and vector spaces.
-/

@[to_additive (attr := fun_prop)]
theorem dsmooth_one {M X : Type*} [DiffeologicalSpace M] [One M] [DiffeologicalSpace X] :
    DSmooth (1 : X → M) :=
  @dsmooth_const _ _ _ _ 1

class DSmoothAdd (M : Type*) [DiffeologicalSpace M] [Add M] : Prop where
  dsmooth_add : DSmooth fun p : M × M => p.1 + p.2

@[to_additive]
class DSmoothMul (M : Type*) [DiffeologicalSpace M] [Mul M] : Prop where
  dsmooth_mul : DSmooth fun p : M × M => p.1 * p.2

section DSmoothMul

variable {M X : Type*} [DiffeologicalSpace M] [Mul M] [DSmoothMul M] [DiffeologicalSpace X]

@[to_additive]
instance : DSmoothMul Mᵒᵈ :=
  ‹DSmoothMul M›

@[to_additive]
theorem dsmooth_mul : DSmooth fun p : M × M => p.1 * p.2 :=
  DSmoothMul.dsmooth_mul

-- TODO: instance on ULift

@[to_additive]
instance DSmoothMul.to_dsmoothSMul : DSmoothSMul M M :=
  ⟨dsmooth_mul⟩

@[to_additive]
instance DSmoothMul.to_dsmoothSMul_op : DSmoothSMul Mᵐᵒᵖ M :=
  ⟨dsmooth_mul.comp <| dsmooth_swap.comp <| MulOpposite.dsmooth_unop.prod_map dsmooth_id⟩

@[to_additive (attr := fun_prop)]
theorem DSmooth.mul  {f g : X → M} (hf : DSmooth f) (hg : DSmooth g) :
    DSmooth fun x => f x * g x :=
  dsmooth_mul.comp (hf.prod_mk hg)

@[to_additive]
theorem dsmooth_mul_left (a : M) : DSmooth fun b : M => a * b :=
  dsmooth_const.mul dsmooth_id

@[to_additive]
theorem dsmooth_mul_right (a : M) : DSmooth fun b : M => b * a :=
  dsmooth_id.mul dsmooth_const

@[to_additive]
instance Prod.dsmoothMul {N : Type*} [DiffeologicalSpace N] [Mul N] [DSmoothMul N] :
    DSmoothMul (M × N) :=
  ⟨(dsmooth_fst.fst'.mul dsmooth_fst.snd').prod_mk (dsmooth_snd.fst'.mul dsmooth_snd.snd')⟩

@[to_additive]
instance Pi.dsmoothMul {ι : Type*} {M : ι → Type*} [∀ i, DiffeologicalSpace (M i)]
    [∀ i, Mul (M i)] [∀ i, DSmoothMul (M i)] : DSmoothMul (∀ i, M i) where
  dsmooth_mul :=
    dsmooth_pi fun i => (dsmooth_apply i).fst'.mul (dsmooth_apply i).snd'

-- TODO: DSmoothMul instance on discrete spaces, once those are available as a typeclass

/-- For any monoid homomorphism to a smooth monoid, the induced diffeology makes the
  action on the domain a smooth monoid too.
  TODO: weaken assumption from `Induction f` (which includes injectivity of `f`) to just
  `dM = dN.induced f`. -/
@[to_additive]
theorem Induction.dsmoothMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    [DiffeologicalSpace M] [DiffeologicalSpace N] [DSmoothMul N] (f : F) (hf : Induction f) :
    DSmoothMul M :=
  ⟨(hf.dsmoothSMul hf.dsmooth (map_mul f _ _)).1⟩

-- TODO: remove injectivity hypothesis -/
@[to_additive]
theorem dsmoothMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    [DiffeologicalSpace N] [DSmoothMul N] (f : F) (hf : Function.Injective f):
    @DSmoothMul M (DiffeologicalSpace.induced f ‹_›) _ :=
  letI := DiffeologicalSpace.induced f ‹_›
  Induction.dsmoothMul f ⟨hf,rfl⟩

end DSmoothMul

@[to_additive]
instance Subsemigroup.dsmoothMul {M : Type*} [DiffeologicalSpace M] [Semigroup M] [DSmoothMul M]
    (S : Subsemigroup M) : DSmoothMul S :=
  Induction.dsmoothMul ({ toFun := (↑), map_mul' := fun _ _ => rfl} : MulHom S M)
    ⟨Subtype.val_injective,rfl⟩

section Monoid

variable {M : Type*} [DiffeologicalSpace M] [Monoid M] [DSmoothMul M]

@[to_additive]
instance Submonoid.dsmoothMul (S : Submonoid M) : DSmoothMul S :=
  S.toSubsemigroup.dsmoothMul

@[to_additive]
theorem dsmooth_pow : ∀ n : ℕ, DSmooth fun a : M => a ^ n
  | 0 => by simp [dsmooth_const]
  | k + 1 => by simp_rw [pow_succ']; exact dsmooth_id.mul (dsmooth_pow _)

-- TODO: adapt `AddMonoid.continuousConstSMul_nat` and `AddMonoid.continuousSMul_nat`

@[to_additive (attr := fun_prop)]
theorem DSmooth.pow {X : Type*} [DiffeologicalSpace X] {f : X → M} (h : DSmooth f) (n : ℕ) :
    DSmooth fun b => f b ^ n :=
  (dsmooth_pow n).comp h

-- TODO: adapt `IsScalarTower.continuousConstSMul` and `SMulCommClass.continuousConstSMul`

end Monoid

namespace MulOpposite

/-- If multiplication is smooth in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is smooth in `α`, then it also is in `αᵃᵒᵖ`."]
instance {M : Type*} [DiffeologicalSpace M] [Mul M] [DSmoothMul M] : DSmoothMul Mᵐᵒᵖ :=
  ⟨dsmooth_op.comp (dsmooth_unop.snd'.mul dsmooth_unop.fst')⟩

end MulOpposite

namespace Units

open MulOpposite

variable {M : Type*} [DiffeologicalSpace M] [Monoid M] [DSmoothMul M]

/-- If multiplication on a monoid is smooth, then multiplication on the units of the monoid,
with respect to the induced diffeology, is also smooth. -/
@[to_additive "If addition on an additive monoid is smooth, then addition on the additive units
of the monoid, with respect to the induced diffeology, is also smooth."]
instance : DSmoothMul Mˣ :=
  induction_embedProduct.dsmoothMul (embedProduct M)

@[to_additive]
theorem DSmooth.units_map {N : Type*} [DiffeologicalSpace N] [Monoid N]
    (f : M →* N) (hf : DSmooth f) : DSmooth (Units.map f) :=
  Units.dsmooth_iff.2 ⟨hf.comp Units.dsmooth_val, hf.comp Units.dsmooth_coe_inv⟩

end Units

@[to_additive]
theorem dsmoothMul_sInf {M : Type*} [Mul M] {D : Set (DiffeologicalSpace M)}
    (h : ∀ d ∈ D, @DSmoothMul M d _) : @DSmoothMul M (sInf D) _ :=
  letI := sInf D
  ⟨dsmooth_sInf_rng.2 fun t ht =>
    dsmooth_sInf_dom₂ ht ht (@DSmoothMul.dsmooth_mul M t _ (h t ht))⟩

@[to_additive]
theorem dsmoothMul_iInf {M ι : Type*} [Mul M] {D : ι → DiffeologicalSpace M}
    (h' : ∀ i, @DSmoothMul M (D i) _) : @DSmoothMul M (⨅ i, D i) _ := by
  rw [← sInf_range]
  exact dsmoothMul_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem dsmoothMul_inf {M : Type*} [Mul M] {d₁ d₂ : DiffeologicalSpace M}
    (h₁ : @DSmoothMul M d₁ _) (h₂ : @DSmoothMul M d₂ _) : @DSmoothMul M (d₁ ⊓ d₂) _ := by
  rw [inf_eq_iInf]
  refine' dsmoothMul_iInf fun b => _
  cases b <;> assumption
