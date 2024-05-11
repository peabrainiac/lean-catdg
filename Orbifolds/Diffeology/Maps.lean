import Orbifolds.Diffeology.Basic

set_option autoImplicit false

section Induced

def DiffeologicalSpace.induced {X Y : Type*} (f : X → Y) (dY : DiffeologicalSpace Y) :
    DiffeologicalSpace X where
  plots n := {p | f ∘ p ∈ plots n}
  constant_plots x := constant_plots (f x)
  plot_reparam {n m p g} := fun hp hg => isPlot_reparam hp hg

def DiffeologicalSpace.coinduced {X Y : Type*} (f : X → Y) (d : DiffeologicalSpace X) :
    DiffeologicalSpace Y where
  plots n := {p | (∃ y, p = fun _ => y) ∨ ∃ p' ∈ plots n, p = f ∘ p'}
  constant_plots x := Or.inl ⟨x,rfl⟩
  plot_reparam {n m p g} := fun hp hg => Or.rec (fun ⟨y,hy⟩ => Or.inl ⟨y,hy ▸ rfl⟩)
    (fun ⟨p',hp'⟩ => Or.inr ⟨p' ∘ g,isPlot_reparam hp'.1 hg,hp'.2 ▸ rfl⟩) hp

variable {X Y : Type*} [dX : DiffeologicalSpace X] [dY : DiffeologicalSpace Y]

def Induction (f : X → Y) : Prop := Function.Injective f ∧ dX = dY.induced f

def Subduction (f : X → Y) : Prop := Function.Surjective f ∧ dY = dX.coinduced f

protected theorem Induction.dsmooth {f : X → Y} (hf : Induction f) : DSmooth f :=
  fun n p hp => by rw [hf.2] at hp; exact hp

protected theorem Subduction.dsmooth {f : X → Y} (hf : Subduction f) : DSmooth f :=
  fun n p hp => by rw [hf.2]; exact Or.inr ⟨p,hp,rfl⟩

end Induced
