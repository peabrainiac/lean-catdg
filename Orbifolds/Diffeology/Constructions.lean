import Orbifolds.Diffeology.Maps

set_option autoImplicit false

open TopologicalSpace

section Constructions

instance instDiffeologicalSpaceSubtype {X : Type*} [DiffeologicalSpace X] {p : X → Prop} :
    DiffeologicalSpace (Subtype p) :=
  DiffeologicalSpace.induced ((↑) : _ → X) inferInstance

-- `Pi.diffeologicalSpace` is currently already defined in `Orbifolds.Diffeology.Basic`.

end Constructions

section Subtype

variable {X : Type*} [DiffeologicalSpace X] {s : Set X}

theorem induction_subtype_val : Induction ((↑) : s → X) :=
  ⟨Subtype.coe_injective,rfl⟩

theorem dsmooth_subtype_val : DSmooth ((↑) : s → X) :=
  induction_subtype_val.dsmooth

/-- TODO. I think this requires a diffeomorphism in the sense of `ContDiff ℝ ⊤` from ℝⁿ to
small balls in it, but should follow easily after that. -/
protected theorem IsOpen.dTopCompatible [TopologicalSpace X] [DTopCompatible X] (hs : IsOpen s) :
    DTopCompatible s := ⟨by ext t; sorry⟩

end Subtype

section Pi

variable {ι : Type*} {Y : ι → Type*} [(i : ι) → DiffeologicalSpace (Y i)]
  {X : Type*} [DiffeologicalSpace X] {f : X → ((i : ι) → Y i)}

theorem dsmooth_pi_iff : DSmooth f ↔ ∀ i, DSmooth fun x => f x i := by
  simp only [dsmooth_def,@forall_comm ι _ _]; rfl

@[fun_prop]
theorem dsmooth_pi (h : ∀ i, DSmooth fun a => f a i) : DSmooth f :=
  dsmooth_pi_iff.2 h

@[fun_prop]
theorem dsmooth_apply (i : ι) : DSmooth fun p : (i : ι) → Y i => p i :=
  dsmooth_pi_iff.1 dsmooth_id i

-- TODO. something like this should be true, but I haven't yet figured out the exact details.
instance [Fintype ι] [(i : ι) → TopologicalSpace (Y i)] [(i : ι) → LocallyCompactSpace (Y i)]
    [(i : ι) → DTopCompatible (Y i)] : DTopCompatible ((i : ι) → Y i) := ⟨by
  ext s; rw [isOpen_pi_iff',isOpen_iff_preimages_plots]
  refine' ⟨fun h => _, fun h n p hp => _⟩
  all_goals sorry⟩

end Pi
