import Orbifolds.Diffeology.Basic
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

section Induced

def DiffeologicalSpace.induced {X Y : Type*} (f : X → Y) (dY : DiffeologicalSpace Y) :
    DiffeologicalSpace X where
  plots n := {p | f ∘ p ∈ plots n}
  constant_plots x := constant_plots (f x)
  plot_reparam := isPlot_reparam
  locality {_ _ hu p} := locality (hu := hu) (p := f ∘ p)

open IsLocallyConstant PartialHomeomorph in
def DiffeologicalSpace.coinduced {X Y : Type*} (f : X → Y) (dX : DiffeologicalSpace X) :
    DiffeologicalSpace Y where
  plots n := {p | (∃ y, p = fun _ => y) ∨ ∃ p' ∈ plots n, p = f ∘ p'}
  constant_plots x := Or.inl ⟨x,rfl⟩
  plot_reparam {n m p g} := fun hp hg => Or.rec (fun ⟨y,hy⟩ => Or.inl ⟨y,hy ▸ rfl⟩)
    (fun ⟨p',hp'⟩ => Or.inr ⟨p' ∘ g,isPlot_reparam hp'.1 hg,hp'.2 ▸ rfl⟩) hp
  locality {n u hu p} := fun h {m g} hgu hg => by
    dsimp
    have := Nonempty.map p inferInstance
    have h'' : ∀ x : Eucl m, ∃ v : Set (Eucl m), x ∈ v ∧ IsOpen v ∧ True := by sorry
    have h' := (isClopen_iff (s := (p ∘ g) ⁻¹' Set.range f)).1 ⟨by
      refine' isOpen_compl_iff.1 <| isOpen_iff_mem_nhds.2 fun x hx => _
      let ⟨v,hvu,hxv,hv,hv'⟩ := h (g x) (hgu x)
      let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 hv (g x) hxv
      have h := @hv' n (univBall (g x) ε) (fun x' => by
        have h := (univBall (g x) ε).map_source (x := x')
        rw [univBall_source, univBall_target (g x) hε] at h
        exact Set.mem_of_mem_of_subset (h (Set.mem_univ _)) hε') contDiff_univBall
      obtain ⟨y,hy⟩ | h := h
      · sorry
      · sorry,by
      refine' isOpen_iff_mem_nhds.2 fun x hx => _
      sorry⟩
    obtain h' | h' := h'
    have := fun p' => @locality X dX n u hu p' (fun x' hxu' => by
      let ⟨v,hvu,hxv',hv,hv'⟩ := h x' hxu'
      exact ⟨v,hvu,hxv',hv,fun {m g} hgu hg => by
        have := @hv' m g hgu hg
        sorry⟩)
    · refine' Or.inl <| exists_eq_const <| (iff_exists_open _).2 fun x => _
      let ⟨v,hvu,hxv,hv,hv'⟩ := h (g x) (hgu x)
      refine' ⟨g ⁻¹' v,hv.preimage hg.continuous,hxv,_⟩
      sorry
    · sorry

variable {X Y : Type*} [dX : DiffeologicalSpace X] [dY : DiffeologicalSpace Y]

def Induction (f : X → Y) : Prop := Function.Injective f ∧ dX = dY.induced f

def Subduction (f : X → Y) : Prop := Function.Surjective f ∧ dY = dX.coinduced f

protected theorem Induction.dsmooth {f : X → Y} (hf : Induction f) : DSmooth f :=
  fun n p hp => by rw [hf.2] at hp; exact hp

protected theorem Subduction.dsmooth {f : X → Y} (hf : Subduction f) : DSmooth f :=
  fun n p hp => by rw [hf.2]; exact Or.inr ⟨p,hp,rfl⟩

end Induced
