import Orbifolds.Diffeology.Algebra.Monoid

/-!
# Diffeological groups
Adapted from `Mathlib.Topology.Algebra.Group.Basic`.
-/

set_option autoImplicit false

universe u v

section DSmoothMulGroup

variable {G : Type*} [DiffeologicalSpace G] [Group G] [DSmoothMul G]

@[to_additive]
protected def DDiffeomorph.mulLeft (a : G) : G ᵈ≃ G :=
  { Equiv.mulLeft a with
    dsmooth_toFun := dsmooth_mul_left a
    dsmooth_invFun := dsmooth_mul_left a⁻¹ }

@[to_additive (attr := simp)]
theorem DDiffeomorph.coe_mulLeft (a : G) : ⇑(DDiffeomorph.mulLeft a) = (a * ·) := rfl

@[to_additive]
theorem DDiffeomorph.mulLeft_symm (a : G) :
    (DDiffeomorph.mulLeft a).symm = DDiffeomorph.mulLeft a⁻¹ := by
  ext; rfl

@[to_additive]
protected def DDiffeomorph.mulRight (a : G) : G ᵈ≃ G :=
  { Equiv.mulRight a with
    dsmooth_toFun := dsmooth_mul_right a
    dsmooth_invFun := dsmooth_mul_right a⁻¹ }

@[to_additive (attr := simp)]
lemma DDiffeomorph.coe_mulRight (a : G) : ⇑(DDiffeomorph.mulRight a) = (· * a) := rfl

@[to_additive]
theorem DDiffeomorph.mulRight_symm (a : G) :
    (DDiffeomorph.mulRight a).symm = DDiffeomorph.mulRight a⁻¹ := by
  ext; rfl

end DSmoothMulGroup

/-!
### `DSmoothInv` and `DSmoothNeg`
-/

/-- Class saying that negation in a type is smooth. A diffeological additive group is then
  a type with the instances `AddGroup G`, `DSmoothAdd G` and `DSmoothNeg G`. -/
class DSmoothNeg (G : Type*) [DiffeologicalSpace G] [Neg G] : Prop where
  dsmooth_neg : DSmooth fun a : G => -a

export DSmoothNeg (dsmooth_neg)

/-- Class saying that inversion in a type is smooth. A diffeological group is then
  a type with the instances `Group G`, `DSmoothMul G` and `DSmoothInv G`. -/
@[to_additive]
class DSmoothInv (G : Type*) [DiffeologicalSpace G] [Inv G] : Prop where
  dsmooth_inv : DSmooth fun a : G => a⁻¹

export DSmoothInv (dsmooth_inv)

section DSmoothInv

variable {G : Type*} [DiffeologicalSpace G] [Inv G] [DSmoothInv G]

@[to_additive]
instance : DSmoothInv (ULift G) :=
  ⟨dsmooth_uLift_up.comp (dsmooth_inv.comp dsmooth_uLift_down)⟩

@[to_additive (attr := fun_prop)]
theorem DSmooth.inv {X : Type*} [DiffeologicalSpace X] {f : X → G} (hf : DSmooth f) :
    DSmooth fun x => (f x)⁻¹ :=
  dsmooth_inv.comp hf

@[to_additive]
instance Prod.dsmoothInv {H : Type*} [DiffeologicalSpace H] [Inv H] [DSmoothInv H] :
    DSmoothInv (G × H) :=
  ⟨dsmooth_inv.fst'.prod_mk dsmooth_inv.snd'⟩

@[to_additive]
instance Pi.dsmoothInv {ι : Type*} {G : ι → Type*} [∀ i, DiffeologicalSpace (G i)]
    [∀ i, Inv (G i)] [∀ i, DSmoothInv (G i)] : DSmoothInv (∀ i, G i) :=
  ⟨dsmooth_pi fun i => (dsmooth_apply i).inv⟩

-- TODO: DSmoothInv instance on discrete spaces, once those are available as a typeclass

instance {H : Type*} [DiffeologicalSpace H] [Inv H] [DSmoothInv H] :
    DSmoothNeg (Additive H) :=
  ⟨@dsmooth_inv H _ _ _⟩

instance {H : Type*} [DiffeologicalSpace H] [Neg H] [DSmoothNeg H] :
    DSmoothInv (Multiplicative H) :=
  ⟨@dsmooth_neg H _ _ _⟩

end DSmoothInv

section DSmoothInvolutiveInv

/-- Inversion in a diffeological group as a diffeomorphism. -/
@[to_additive "Negation in a diffeological group as a diffeomorphism."]
protected def Diffeomorph.inv (G : Type*) [DiffeologicalSpace G] [InvolutiveInv G]
    [DSmoothInv G] : G ᵈ≃ G :=
  { Equiv.inv G with
    dsmooth_toFun := dsmooth_inv
    dsmooth_invFun := dsmooth_inv }

@[to_additive (attr := simp)]
lemma Diffeomorph.coe_inv {G : Type*} [DiffeologicalSpace G] [InvolutiveInv G] [DSmoothInv G] :
    ⇑(Diffeomorph.inv G) = Inv.inv := rfl

end DSmoothInvolutiveInv

@[to_additive]
theorem dsmoothInv_sInf {G : Type*} [Inv G] {D : Set (DiffeologicalSpace G)}
    (h : ∀ d ∈ D, @DSmoothInv G d _) : @DSmoothInv G (sInf D) _ :=
  letI := sInf D
  ⟨dsmooth_sInf_rng.2 fun d hd => dsmooth_sInf_dom hd
    (@DSmoothInv.dsmooth_inv G d _ (h d hd))⟩

@[to_additive]
theorem dsmoothInv_iInf {G ι : Type*} [Inv G] {D : ι → DiffeologicalSpace G}
    (h' : ∀ i, @DSmoothInv G (D i) _) : @DSmoothInv G (⨅ i, D i) _ := by
  rw [←sInf_range]; exact dsmoothInv_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem dsmoothInv_inf {G : Type*} [Inv G] {d₁ d₂ : DiffeologicalSpace G}
    (h₁ : @DSmoothInv G d₁ _) (h₂ : @DSmoothInv G d₂ _) : @DSmoothInv G (d₁ ⊓ d₂) _ :=
  inf_eq_iInf d₁ d₂ ▸ dsmoothInv_iInf fun b => (by cases b <;> assumption)

-- TODO: remove injectivity hypothesis
@[to_additive]
theorem Induction.dsmoothInv {G H : Type*} [Inv G] [Inv H] [DiffeologicalSpace G]
    [DiffeologicalSpace H] [DSmoothInv H] {f : G → H} (hf : Induction f)
    (hf_inv : ∀ x, f x⁻¹ = (f x)⁻¹) : DSmoothInv G :=
  ⟨hf.dsmooth_iff.2 <| by simpa only [Function.comp_def, hf_inv] using hf.dsmooth.inv⟩

/-!
### Diffeological groups

A diffeological group is a group which is also a diffeological space in such a way that
the multiplication and inversion operations are smooth.
-/

section DiffeologicalGroup

/-- A diffeological (additive) group is a group in which the addition and negation operations
  are dsmooth. -/
class DiffeologicalAddGroup (G : Type*) [DiffeologicalSpace G] [AddGroup G] extends
  DSmoothAdd G, DSmoothNeg G : Prop

/-- A diffeological group is a group in which the multiplication and inversion operations are
  smooth. -/
@[to_additive]
class DiffeologicalGroup (G : Type*) [DiffeologicalSpace G] [Group G] extends DSmoothMul G,
  DSmoothInv G : Prop

section Conj

-- TODO: adapt `ConjAct.units_continuousConstSMul`

variable {G : Type*} [DiffeologicalSpace G] [Inv G] [Mul G] [DSmoothMul G]

/-- Conjugation is jointly smooth on `G × G` when both `mul` and `inv` are smooth. -/
@[to_additive
  "Conjugation is jointly smooth on `G × G` when both `add` and `neg` are smooth."]
theorem DiffeologicalGroup.dsmooth_conj_prod [DSmoothInv G] :
    DSmooth fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  dsmooth_mul.mul (dsmooth_inv.comp dsmooth_fst)

/-- Conjugation by a fixed element is smooth when `mul` is smooth. -/
@[to_additive
  "Conjugation by a fixed element is smooth when `add` is smooth."]
theorem DiffeologicalGroup.dsmooth_conj (g : G) : DSmooth fun h : G => g * h * g⁻¹ :=
  (dsmooth_mul_right g⁻¹).comp (dsmooth_mul_left g)

/-- Conjugation acting on fixed element of the group is smooth when both `mul` and
`inv` are smooth. -/
@[to_additive (attr := continuity)
  "Conjugation acting on fixed element of the additive group is smooth when both
    `add` and `neg` are smooth."]
theorem DiffeologicalGroup.dsmooth_conj' [DSmoothInv G] (h : G) :
    DSmooth fun g : G => g * h * g⁻¹ :=
  (dsmooth_mul_right h).mul dsmooth_inv

end Conj

variable {G : Type*} [DiffeologicalSpace G] [Group G] [DiffeologicalGroup G]

instance : DiffeologicalGroup (ULift G) where

section ZPow

@[to_additive]
theorem dsmooth_zpow : ∀ z : ℤ, DSmooth fun a : G => a ^ z
  | Int.ofNat n => by simpa using dsmooth_pow n
  | Int.negSucc n => by simpa using (dsmooth_pow (n + 1)).inv

-- TODO: adapt `AddGroup.continuousConstSMul_int`, `AddGroup.continuousSMul_int`

--#check continuous_prod_of_discrete_left

@[to_additive (attr := fun_prop)]
theorem DSmooth.zpow {X : Type*} [DiffeologicalSpace X] {f : X → G} (h : DSmooth f) (z : ℤ) :
    DSmooth fun b => f b ^ z :=
  (dsmooth_zpow z).comp h

end ZPow

variable {H : Type*} [DiffeologicalSpace H] [Group H] [DiffeologicalGroup H]

@[to_additive]
instance {H : Type*} [DiffeologicalSpace H] [Group H] [DiffeologicalGroup H] :
    DiffeologicalGroup (G × H) where

@[to_additive]
instance Pi.diffeologicalGroup {ι : Type*} {G : ι → Type*} [∀ i, DiffeologicalSpace (G i)]
    [∀ i, Group (G i)] [∀ i, DiffeologicalGroup (G i)] : DiffeologicalGroup (∀ i, G i) where

open MulOpposite

@[to_additive]
instance {G : Type*} [DiffeologicalSpace G] [Inv G] [DSmoothInv G] : DSmoothInv Gᵐᵒᵖ :=
  by sorry--opDDiffeomorph.symm.induction.dsmoothInv unop_inv

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance {G : Type*} [DiffeologicalSpace G] [Group G] [DiffeologicalGroup G] :
  DiffeologicalGroup Gᵐᵒᵖ where

variable (G)

/-- The map `(x, y) ↦ (x, x * y)` as a diffeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism. This is a shear mapping."]
protected def DDiffeomorph.shearMulRight : G × G ᵈ≃ G × G :=
  { Equiv.prodShear (Equiv.refl _) Equiv.mulLeft with
    dsmooth_toFun := dsmooth_fst.prod_mk dsmooth_mul
    dsmooth_invFun := dsmooth_fst.prod_mk <| dsmooth_fst.inv.mul dsmooth_snd }

@[to_additive (attr := simp)]
theorem DDiffeomorph.shearMulRight_coe :
    ⇑(DDiffeomorph.shearMulRight G) = fun z : G × G => (z.1, z.1 * z.2) :=
  rfl

@[to_additive (attr := simp)]
theorem DDiffeomorph.shearMulRight_symm_coe :
    ⇑(DDiffeomorph.shearMulRight G).symm = fun z : G × G => (z.1, z.1⁻¹ * z.2) :=
  rfl

variable {G}

omit [DiffeologicalSpace H] [Group H] [DiffeologicalGroup H] in
-- TODO: remove injectivity hypothesis
@[to_additive]
protected theorem Induction.diffeologicalGroup {F : Type*} [Group H] [DiffeologicalSpace H]
    [FunLike F H G] [MonoidHomClass F H G] (f : F) (hf : Induction f) : DiffeologicalGroup H :=
  { toDSmoothMul := hf.dsmoothMul _
    toDSmoothInv := hf.dsmoothInv (map_inv f) }

omit [DiffeologicalSpace H] [Group H] [DiffeologicalGroup H] in
-- TODO: remove injectivity hypothesis
@[to_additive]
theorem diffeologicalGroup_induced {F : Type*} [Group H] [FunLike F H G] [MonoidHomClass F H G]
    (f : F) (hf : Function.Injective f):
    @DiffeologicalGroup H (DiffeologicalSpace.induced f ‹_›) _ :=
  letI := DiffeologicalSpace.induced f ‹_›
  Induction.diffeologicalGroup f ⟨hf,rfl⟩

namespace Subgroup

@[to_additive]
instance (S : Subgroup G) : DiffeologicalGroup S :=
  Induction.diffeologicalGroup S.subtype induction_subtype_val

end Subgroup

end DiffeologicalGroup

section QuotientDiffeologicalGroup

@[to_additive]
instance QuotientGroup.Quotient.diffeologicalSpace {G : Type*} [Group G] [DiffeologicalSpace G]
    (N : Subgroup G) : DiffeologicalSpace (G ⧸ N) :=
  instDiffeologicalSpaceQuotient

open QuotientGroup

variable {G : Type*} [DiffeologicalSpace G] [Group G] [DiffeologicalGroup G]
  (N : Subgroup G)-- (n : N.Normal)

omit [DiffeologicalGroup G] in
@[to_additive]
theorem QuotientGroup.subduction_coe : Subduction ((↑) : G → G ⧸ N) :=
  subduction_quotient_mk'

@[to_additive]
instance diffeologicalGroup_quotient [N.Normal] : DiffeologicalGroup (G ⧸ N) where
  dsmooth_mul := ((subduction_coe N).prod_map (subduction_coe N)).dsmooth_iff.2
    (dsmooth_quot_mk.comp dsmooth_mul)
  dsmooth_inv := (subduction_coe N).dsmooth_iff.2
    (dsmooth_quot_mk.comp dsmooth_inv)

end QuotientDiffeologicalGroup

/-- A typeclass saying that `p : G × G ↦ p.1 - p.2` is a smooth function. This property
automatically holds for diffeological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class DSmoothSub (G : Type*) [DiffeologicalSpace G] [Sub G] : Prop where
  dsmooth_sub : DSmooth fun p : G × G => p.1 - p.2

/-- A typeclass saying that `p : G × G ↦ p.1 / p.2` is a smooth function. This property
automatically holds for diffeological groups. Lemmas using this class have primes.
The unprimed version is for `GroupWithZero`. -/
@[to_additive]
class DSmoothDiv (G : Type*) [DiffeologicalSpace G] [Div G] : Prop where
  dsmooth_div' : DSmooth fun p : G × G => p.1 / p.2

@[to_additive]
instance (priority := 100) DiffeologicalGroup.to_dsmoothDiv {G : Type*} [DiffeologicalSpace G]
    [Group G] [DiffeologicalGroup G] : DSmoothDiv G :=
  ⟨by simp_rw [div_eq_mul_inv]; exact dsmooth_fst.mul dsmooth_snd.inv⟩

export DSmoothSub (dsmooth_sub)

export DSmoothDiv (dsmooth_div')

section DSmoothDiv

variable {G : Type*} [DiffeologicalSpace G] [Group G] [DiffeologicalGroup G]

@[to_additive (attr := fun_prop) sub]
theorem DSmooth.div' {X : Type*} [DiffeologicalSpace X] {f g : X → G}
    (hf : DSmooth f) (hg : DSmooth g) : DSmooth fun x => f x / g x :=
  dsmooth_div'.comp (hf.prod_mk hg : _)

@[to_additive dsmooth_sub_left]
lemma dsmooth_div_left' (g : G) : DSmooth (g / ·) := dsmooth_const.div' dsmooth_id

@[to_additive dsmooth_sub_right]
lemma dsmooth_div_right' (g : G) : DSmooth (· / g) := dsmooth_id.div' dsmooth_const

end DSmoothDiv

section DivInvDiffeologicalGroup

variable {G : Type*} [DiffeologicalSpace G] [Group G] [DiffeologicalGroup G]

/-- A version of `DDiffeomorph.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps! (config := { simpRhs := true }))
  " A version of `DDiffeomorph.addLeft a (-b)` that is defeq to `a - b`. "]
def DDiffeomorph.divLeft (g : G) : G ᵈ≃ G :=
  { Equiv.divLeft g with
    dsmooth_toFun := dsmooth_div_left' g
    dsmooth_invFun := dsmooth_inv.mul dsmooth_const }

/-- A version of `DDiffeomorph.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps! (config := { simpRhs := true }))
  "A version of `DDiffeomorph.addRight (-a) b` that is defeq to `b - a`. "]
def DDiffeomorph.divRight (g : G) : G ᵈ≃ G :=
  { Equiv.divRight g with
    dsmooth_toFun := dsmooth_div_right' g
    dsmooth_invFun := dsmooth_id.mul dsmooth_const }

end DivInvDiffeologicalGroup

instance {G : Type*} [DiffeologicalSpace G] [Group G] [DiffeologicalGroup G] :
    DiffeologicalAddGroup (Additive G) where

instance {G : Type*} [DiffeologicalSpace G] [AddGroup G] [DiffeologicalAddGroup G] :
    DiffeologicalGroup (Multiplicative G) where

-- TODO: adapt `QuotientGroup.continuousConstSMul`

/-- A group with smooth inversion is diffeomorphic to its units. -/
@[to_additive "An additive group with smooth negation is homeomorphic to its
  additive units."]
def toUnits_ddiffeomorph {G : Type*} [Group G] [DiffeologicalSpace G] [DSmoothInv G] :
    G ᵈ≃ Gˣ where
  toEquiv := toUnits.toEquiv
  dsmooth_toFun := Units.dsmooth_iff.2 ⟨dsmooth_id, dsmooth_inv⟩
  dsmooth_invFun := Units.dsmooth_val

namespace Units

open MulOpposite (dsmooth_op dsmooth_unop)

variable {M N : Type*} [Monoid M] [DiffeologicalSpace M] [Monoid N] [DiffeologicalSpace N]

@[to_additive]
instance [DSmoothMul M] : DiffeologicalGroup Mˣ where
  dsmooth_inv := Units.dsmooth_iff.2 <| ⟨dsmooth_coe_inv, dsmooth_val⟩

/-- The diffeological group isomorphism between the units of a product of two monoids,
  and the product of the units of each monoid. -/
@[to_additive
  "The diffeological group isomorphism between the additive units of a product of two
  additive monoids, and the product of the additive units of each additive monoid."]
def DDiffeomorph.prodUnits : (M × N)ˣ ᵈ≃ Mˣ × Nˣ where
  toEquiv := MulEquiv.prodUnits.toEquiv
  dsmooth_toFun := (dsmooth_fst.units_map (MonoidHom.fst M N)).prod_mk
    (dsmooth_snd.units_map (MonoidHom.snd M N))
  dsmooth_invFun := Units.dsmooth_iff.2 ⟨dsmooth_val.fst'.prod_mk dsmooth_val.snd',
    dsmooth_coe_inv.fst'.prod_mk dsmooth_coe_inv.snd'⟩

end Units

@[to_additive]
theorem diffeologicalGroup_sInf {G : Type*} [Group G] {D : Set (DiffeologicalSpace G)}
    (h : ∀ d ∈ D, @DiffeologicalGroup G d _) : @DiffeologicalGroup G (sInf D) _ :=
  letI := sInf D
  { toDSmoothInv :=
      @dsmoothInv_sInf _ _ _ fun d hd => @DiffeologicalGroup.toDSmoothInv G d _ <| h d hd
    toDSmoothMul :=
      @dsmoothMul_sInf _ _ _ fun d hd => @DiffeologicalGroup.toDSmoothMul G d _ <| h d hd }

@[to_additive]
theorem diffeologicalGroup_iInf {G ι : Type*} [Group G] {D : ι → DiffeologicalSpace G}
    (h' : ∀ i, @DiffeologicalGroup G (D i) _) : @DiffeologicalGroup G (⨅ i, D i) _ := by
  rw [←sInf_range]; exact diffeologicalGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem diffeologicalGroup_inf {G : Type*} [Group G] {d₁ d₂ : DiffeologicalSpace G}
    (h₁ : @DiffeologicalGroup G d₁ _) (h₂ : @DiffeologicalGroup G d₂ _) :
    @DiffeologicalGroup G (d₁ ⊓ d₂) _ :=
  inf_eq_iInf d₁ d₂ ▸ diffeologicalGroup_iInf fun b => (by cases b <;> assumption)

/-!
### Lattice of group diffeologies

We define a type class `GroupDiffeology G` which endows a group `G` with a diffeology such
that all group operations are smooth.

Group diffeologies on a fixed group `G` are ordered by inclusion. They form a complete
lattice, with `⊥` the discrete diffeology and `⊤` the indiscrete diffeology.

Any function `f : G → H` induces `coinduced f : DiffeologicalSpace G → GroupDiffeology H`.

An additive version `AddGroupDiffeology G` is defined as well.
-/

/-- An additive group diffeology on a group `G` is a diffeology that makes `G` into an
  additive diffeological group. -/
structure AddGroupDiffeology (G : Type u) [AddGroup G] extends DiffeologicalSpace G,
  DiffeologicalAddGroup G : Type u

/-- A group diffeology on a group `G` is a diffeology that makes `G` into a
  diffeological group. -/
@[to_additive]
structure GroupDiffeology (G : Type u) [Group G] extends DiffeologicalSpace G,
  DiffeologicalGroup G : Type u

namespace GroupDiffeology

variable {G : Type*} [Group G]

/-- A version of the global `dsmooth_mul` suitable for dot notation. -/
@[to_additive "A version of the global `dsmooth_add` suitable for dot notation."]
theorem dsmooth_mul' (d : GroupDiffeology G) :
    haveI := d.toDiffeologicalSpace
    DSmooth fun p : G × G => p.1 * p.2 := by
  letI := d.toDiffeologicalSpace
  haveI := d.toDiffeologicalGroup
  exact dsmooth_mul

/-- A version of the global `dsmooth_inv` suitable for dot notation. -/
@[to_additive "A version of the global `dsmooth_neg` suitable for dot notation."]
theorem dsmooth_inv' (d : GroupDiffeology G) :
    haveI := d.toDiffeologicalSpace
    DSmooth (Inv.inv : G → G) := by
  letI := d.toDiffeologicalSpace
  haveI := d.toDiffeologicalGroup
  exact dsmooth_inv

@[to_additive]
theorem toDiffeologicalSpace_injective :
    Function.Injective (toDiffeologicalSpace : GroupDiffeology G → DiffeologicalSpace G) :=
  fun f g h => by cases f; cases g; congr

@[to_additive (attr := ext)]
theorem ext' {d₁ d₂ : GroupDiffeology G} (h : d₁.1 = d₂.1) : d₁ = d₂ :=
  toDiffeologicalSpace_injective h

@[to_additive]
instance : PartialOrder (GroupDiffeology G) :=
  PartialOrder.lift toDiffeologicalSpace toDiffeologicalSpace_injective

@[to_additive (attr := simp)]
theorem toDiffeologicalSpace_le {d₁ d₂ : GroupDiffeology G} :
    d₁.1 ≤ d₂.1 ↔ d₁ ≤ d₂ :=
  Iff.rfl

@[to_additive]
instance : Top (GroupDiffeology G) :=
  let _t : DiffeologicalSpace G := ⊤
  ⟨{  dsmooth_mul := dsmooth_top
      dsmooth_inv := dsmooth_top }⟩

@[to_additive (attr := simp)]
theorem toDiffeologicalSpace_top : (⊤ : GroupDiffeology G).toDiffeologicalSpace = ⊤ :=
  rfl

@[to_additive]
instance : Bot (GroupDiffeology G) :=
  let _t : DiffeologicalSpace G := ⊥
  ⟨{  dsmooth_mul := by sorry -- requires knowing that products of discrete spaces are discrete
      dsmooth_inv := by sorry }⟩ -- same thing

@[to_additive (attr := simp)]
theorem toDiffeologicalSpace_bot : (⊥ : GroupDiffeology G).toDiffeologicalSpace = ⊥ :=
  rfl

@[to_additive]
instance : BoundedOrder (GroupDiffeology G) where
  top := ⊤
  le_top x := show x.toDiffeologicalSpace ≤ ⊤ from le_top
  bot := ⊥
  bot_le x := show ⊥ ≤ x.toDiffeologicalSpace from bot_le

@[to_additive]
instance : Min (GroupDiffeology G) where min d₁ d₂ :=
  ⟨d₁.1 ⊓ d₂.1,diffeologicalGroup_inf d₁.2 d₂.2⟩

@[to_additive (attr := simp)]
theorem toDiffeologicalSpace_inf (x y : GroupDiffeology G) : (x ⊓ y).1 = x.1 ⊓ y.1 :=
  rfl

@[to_additive]
instance : SemilatticeInf (GroupDiffeology G) :=
  toDiffeologicalSpace_injective.semilatticeInf _ toDiffeologicalSpace_inf

@[to_additive]
instance : Inhabited (GroupDiffeology G) := ⟨⊤⟩

/-- Infimum of a collection of group diffeologies. -/
@[to_additive "Infimum of a collection of additive group diffeologies"]
instance : InfSet (GroupDiffeology G) where
  sInf D := ⟨sInf (toDiffeologicalSpace '' D),
    diffeologicalGroup_sInf <| Set.forall_mem_image.2 fun d _ => d.2⟩

@[to_additive (attr := simp)]
theorem toDiffeologicalSpace_sInf (s : Set (GroupDiffeology G)) :
    (sInf s).toDiffeologicalSpace = sInf (toDiffeologicalSpace '' s) := rfl

@[to_additive (attr := simp)]
theorem toDiffeologicalSpace_iInf {ι : Type*} (s : ι → GroupDiffeology G) :
    (⨅ i, s i).1 = ⨅ i, (s i).1 :=
  congr_arg sInf (Set.range_comp _ _).symm

@[to_additive]
instance : CompleteSemilatticeInf (GroupDiffeology G) :=
  { inferInstanceAs (InfSet (GroupDiffeology G)),
    inferInstanceAs (PartialOrder (GroupDiffeology G)) with
    sInf_le := fun S a haS => toDiffeologicalSpace_le.1 <| sInf_le ⟨a, haS, rfl⟩
    le_sInf := by
      intro S a hab
      apply (inferInstanceAs (CompleteLattice (DiffeologicalSpace G))).le_sInf
      rintro _ ⟨b, hbS, rfl⟩
      exact hab b hbS }

@[to_additive]
instance : CompleteLattice (GroupDiffeology G) :=
  { inferInstanceAs (BoundedOrder (GroupDiffeology G)),
    inferInstanceAs (SemilatticeInf (GroupDiffeology G)),
    completeLatticeOfCompleteSemilatticeInf _ with
    inf := (· ⊓ ·)
    top := ⊤
    bot := ⊥ }

end GroupDiffeology
