import Orbifolds.Diffeology.Algebra.Constructions
import Mathlib.Topology.Algebra.MulAction

/-!
# Smooth actions by monoids
Adapted from `Mathlib.Topology.Algebra.MulAction`.
For now this just contains a few basic definitions and lemmas, used to build up the theory of
diffeological groups and vector spaces.
-/

set_option autoImplicit false

/-- Class `ContinuousVAdd M X` saying that the additive action `(+ᵥ) : M → X → X`
  is smooth in both arguments. -/
class DSmoothVAdd (M X : Type*) [VAdd M X] [DiffeologicalSpace M] [DiffeologicalSpace X] :
    Prop where
  dsmooth_vadd : DSmooth fun p : M × X => p.1 +ᵥ p.2

export DSmoothVAdd (dsmooth_vadd)

/-- Class `DSmoothSMul M X` saying that the scalar multiplication `(•) : M → X → X`
  is smooth in both arguments. -/
@[to_additive]
class DSmoothSMul (M X : Type*) [SMul M X] [DiffeologicalSpace M] [DiffeologicalSpace X] :
    Prop where
  dsmooth_smul : DSmooth fun p : M × X => p.1 • p.2

export DSmoothSMul (dsmooth_smul)

variable {M X Y : Type*} [DiffeologicalSpace M] [dX : DiffeologicalSpace X]
  [dY : DiffeologicalSpace Y]

@[to_additive]
instance [SMul M X] [DSmoothSMul M X] : DSmoothSMul (ULift M) X :=
  ⟨(dsmooth_smul (M := M)).comp₂ (dsmooth_uLift_down.comp dsmooth_fst) dsmooth_snd⟩

@[to_additive (attr := fun_prop)]
theorem DSmooth.smul [SMul M X] [DSmoothSMul M X] {f : Y → M} {g : Y → X}
    (hf : DSmooth f) (hg : DSmooth g) : DSmooth fun x => f x • g x :=
  dsmooth_smul.comp (hf.prod_mk hg)

@[to_additive]
instance DSmoothSMul.op [SMul M X] [DSmoothSMul M X] [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] :
    DSmoothSMul Mᵐᵒᵖ X := ⟨by
  suffices DSmooth fun p : M × X => MulOpposite.op p.fst • p.snd from
    this.comp (MulOpposite.dsmooth_unop.prod_map dsmooth_id)
  simpa only [op_smul_eq_smul] using (dsmooth_smul : DSmooth fun p : M × X => _)⟩

@[to_additive]
instance MulOpposite.dsmoothSMul [SMul M X] [DSmoothSMul M X] : DSmoothSMul M Xᵐᵒᵖ :=
  ⟨MulOpposite.dsmooth_op.comp <|
      dsmooth_smul.comp <| dsmooth_id.prod_map MulOpposite.dsmooth_unop⟩

/-- For any action homomorphism where the action on the codomain is smooth, the induced
  diffeology makes the action on the domain smooth too.
  TODO: weaken assumption from `Induction g` (which includes injectivity of `g`) to
  just `dY = dX.induced g`. -/
@[to_additive "For any action homomorphism where the action on the codomain is smooth, the induced
  diffeology makes the action on the domain smooth too."]
lemma Induction.dsmoothSMul [SMul M X] [DSmoothSMul M X] {N : Type*} [SMul N Y]
    [DiffeologicalSpace N] {g : Y → X} {f : N → M} (hg : Induction g) (hf : DSmooth f)
    (hsmul : ∀ {c x}, g (c • x) = f c • g x) : DSmoothSMul N Y := ⟨by
  simpa only [hg.dsmooth_iff, Function.comp_def, hsmul]
    using (hf.comp dsmooth_fst).smul <| hg.dsmooth.comp dsmooth_snd⟩

@[to_additive]
instance SMulMemClass.dsmoothSMul [SMul M X] [DSmoothSMul M X] {S : Type*} [SetLike S X]
    [SMulMemClass S M X] (s : S) : DSmoothSMul M s :=
  induction_subtype_val.dsmoothSMul dsmooth_id rfl

section Monoid

variable [Monoid M] [MulAction M X] [DSmoothSMul M X]

@[to_additive]
instance Units.dsmoothSMul : DSmoothSMul Mˣ X :=
  induction_id.dsmoothSMul Units.dsmooth_val rfl

/-- Composing a smooth action with a smooth homomorphism results in a smooth action. -/
@[to_additive]
theorem MulAction.dsmoothSMul_compHom {N : Type*} [DiffeologicalSpace N] [Monoid N]
    {f : N →* M} (hf : DSmooth f) :
    letI : MulAction N X := MulAction.compHom _ f
    DSmoothSMul N X := by
  let _ : MulAction N X := MulAction.compHom _ f
  exact ⟨(hf.comp dsmooth_fst).smul dsmooth_snd⟩

@[to_additive]
instance Submonoid.dsmoothSMul {S : Submonoid M} : DSmoothSMul S X :=
  induction_id.dsmoothSMul dsmooth_subtype_val rfl

end Monoid

instance Subgroup.dsmoothSMul [Group M] [MulAction M X] [DSmoothSMul M X] {S : Subgroup M} :
    DSmoothSMul S X :=
  S.toSubmonoid.dsmoothSMul

@[to_additive]
instance Prod.dsmoothSMul [SMul M X] [SMul M Y] [DSmoothSMul M X] [DSmoothSMul M Y] :
    DSmoothSMul M (X × Y) :=
  ⟨(dsmooth_fst.smul (dsmooth_fst.comp dsmooth_snd)).prod_mk
      (dsmooth_fst.smul (dsmooth_snd.comp dsmooth_snd))⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*} [∀ i, DiffeologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, DSmoothSMul M (γ i)] : DSmoothSMul M (∀ i, γ i) :=
  ⟨dsmooth_pi fun i => (dsmooth_fst.smul dsmooth_snd).comp <|
    dsmooth_fst.prod_mk ((dsmooth_apply i).comp dsmooth_snd)⟩

@[to_additive]
theorem dsmoothSMul_sInf {X : Type*} [SMul M X] {D : Set (DiffeologicalSpace X)}
    (h : ∀ d ∈ D, @DSmoothSMul M X _ _ d) : @DSmoothSMul M X _ _ (sInf D) :=
  @DSmoothSMul.mk M X _ _ (_) <| @sInf_singleton _ _ ‹DiffeologicalSpace M› ▸
    dsmooth_sInf_rng.2 fun t ht => dsmooth_sInf_dom₂ rfl ht
      (@DSmoothSMul.dsmooth_smul _ _ _ _ t (h t ht))

@[to_additive]
theorem dsmoothSMul_iInf {X ι : Type*} [SMul M X] {D : ι → DiffeologicalSpace X}
    (h : ∀ i, @DSmoothSMul M X _ _ (D i)) : @DSmoothSMul M X _ _ (⨅ i, D i) :=
  dsmoothSMul_sInf <| Set.forall_mem_range.mpr h

@[to_additive]
theorem dsmoothSMul_inf {X : Type*} [SMul M X] {d₁ d₂ : DiffeologicalSpace X}
    [@DSmoothSMul M X _ _ d₁] [@DSmoothSMul M X _ _ d₂] : @DSmoothSMul M X _ _ (d₁ ⊓ d₂) :=
  inf_eq_iInf d₁ d₂ ▸ dsmoothSMul_iInf fun b => (by cases b <;> assumption)
