import CatDG.Diffeology.LocallyModelled

universe u

variable {X Y Z : Type u} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]
  {n m k : ℕ} [hX : IsOrbifold n X] [hY : IsOrbifold m Y] [hZ : IsOrbifold k Z]

instance : IsOrbifold (n + m) (X × Y) where
  locally_modelled := fun ⟨x,y⟩ ↦ by
    let _ := @DTop X _; let _ := @DTop Y _
    let ⟨u, hu, hxu, Γ, u', hu', ⟨du⟩⟩ := hX.locally_modelled x
    let ⟨v, hv, hyv, Γ', v', hv', ⟨dv⟩⟩ := hY.locally_modelled y
    have := @IsOrbifold.locallyCompactSpace X DTop _ ⟨rfl⟩ _ hX
    refine ⟨u ×ˢ v, by
      rw [dTop_prod_eq_prod_dTop_of_locallyCompact_left]; exact hu.prod hv, ⟨hxu, hyv⟩, ?_⟩

    sorry
