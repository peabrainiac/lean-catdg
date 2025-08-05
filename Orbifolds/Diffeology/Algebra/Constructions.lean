import Orbifolds.Diffeology.Constructions
import Orbifolds.Diffeology.DDiffeomorph

/-!
# Diffeological space structure on the opposite monoid and on the units group

Defines the `DiffeologicalSpace` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `AddUnits M`.
Adapted from `Mathlib.Topology.Algebra.Constructions`
-/

variable {M X : Type*} [dM : DiffeologicalSpace M]

namespace MulOpposite

/-- The opposite monoid is equipped with the same diffeology as the original. -/
@[to_additive "The opposite monoid is equipped with the same diffeology as the original."]
instance instDiffeologicalSpaceMulOpposite : DiffeologicalSpace Mᵐᵒᵖ :=
  dM.induced (unop : Mᵐᵒᵖ → M)

@[to_additive]
theorem dsmooth_unop : DSmooth (unop : Mᵐᵒᵖ → M) :=
  dsmooth_induced_dom

@[to_additive]
theorem dsmooth_op : DSmooth (op : M → Mᵐᵒᵖ) :=
  dsmooth_induced_rng.2 dsmooth_id

/-- `MulOpposite.op` as a diffeomorphism. -/
@[to_additive (attr := simps!) "`AddOpposite.op` as a diffeomorphism."]
def opDDiffeomorph : M ᵈ≃ Mᵐᵒᵖ where
  toEquiv := opEquiv
  dsmooth_toFun := dsmooth_op
  dsmooth_invFun := dsmooth_unop

end MulOpposite

namespace Units

open MulOpposite

variable [Monoid M] [DiffeologicalSpace X]

/-- The units of a monoid are equipped with the diffeology induced by the embedding
into `M × M`. -/
@[to_additive "The units of a monoid are equipped with the diffeology induced by the embedding
into `M × M`."]
instance instDiffeologicalSpaceUnits : DiffeologicalSpace Mˣ :=
  DiffeologicalSpace.induced (embedProduct M) inferInstance

@[to_additive]
theorem isInduction_embedProduct : IsInduction (embedProduct M) :=
  ⟨⟨rfl⟩, embedProduct_injective _⟩

@[to_additive] lemma diffeology_eq_inf : instDiffeologicalSpaceUnits =
    dM.induced (val : Mˣ → M) ⊓ dM.induced (fun u ↦ ↑u⁻¹ : Mˣ → M) :=
  isInduction_embedProduct.eq_induced

@[to_additive]
theorem dsmooth_embedProduct : DSmooth (embedProduct M) :=
  dsmooth_induced_dom

@[to_additive]
theorem dsmooth_val : DSmooth ((↑) : Mˣ → M) :=
  (@dsmooth_embedProduct M _ _).fst

@[to_additive]
protected theorem dsmooth_iff {f : X → Mˣ} :
    DSmooth f ↔ DSmooth (val ∘ f) ∧ DSmooth (fun x ↦ ↑(f x)⁻¹ : X → M) := by
  simp_rw [isInduction_embedProduct.dsmooth_iff, Function.comp_def, dsmooth_prod_mk]; rfl

@[to_additive]
theorem dsmooth_coe_inv : DSmooth (fun u ↦ ↑u⁻¹ : Mˣ → M) :=
  (Units.dsmooth_iff.1 dsmooth_id).2

end Units
