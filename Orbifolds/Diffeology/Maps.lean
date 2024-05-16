import Orbifolds.Diffeology.Basic
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

section Induced

def DiffeologicalSpace.induced {X Y : Type*} (f : X → Y) (dY : DiffeologicalSpace Y) :
    DiffeologicalSpace X where
  plots n := {p | f ∘ p ∈ plots n}
  constant_plots x := constant_plots (f x)
  plot_reparam := isPlot_reparam
  locality {_ p} := locality (p := f ∘ p)

variable {X Y : Type*} [dX : DiffeologicalSpace X] [dY : DiffeologicalSpace Y]

def Induction (f : X → Y) : Prop := Function.Injective f ∧ dX = dY.induced f

protected theorem Induction.dsmooth {f : X → Y} (hf : Induction f) : DSmooth f :=
  fun n p hp => by rw [hf.2] at hp; exact hp

end Induced
