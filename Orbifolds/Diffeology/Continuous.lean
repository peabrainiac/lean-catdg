import Orbifolds.Diffeology.DSmoothMap
import Orbifolds.ForMathlib.DeltaGeneratedSpace

/-!
# Continuous diffeology

Defines the continuous diffeology on topological spaces, i.e. the diffeology consisting of all
continuous plots. This is used mainly to show in `Orbifolds.Diffeology.DiffCat` that the
D-topology functor has a right adjoint.
See https://ncatlab.org/nlab/show/adjunction+between+topological+spaces+and+diffeological+spaces.
-/

universe u

open Topology

/-- The continuous diffeology on a topological space `X`. -/
def continuousDiffeology (X : Type u) [TopologicalSpace X] : DiffeologicalSpace X :=
  DiffeologicalSpace.mkOfPlotsOn {
    isPlotOn := fun {_ u} _ p => ContinuousOn p u
    isPlotOn_congr := fun _ _ _ h => continuousOn_congr h
    isPlot := fun p => Continuous p
    isPlotOn_univ := continuous_iff_continuousOn_univ.symm
    isPlot_const := fun _ => continuous_const
    isPlotOn_reparam := fun _ _ _ h hp hf => hp.comp hf.continuousOn h.subset_preimage
    locality := fun _ _ h => fun x hxu => by
      let ⟨v,hv,hxv,hv'⟩ := h x hxu
      exact ((hv' x hxv).continuousAt (hv.mem_nhds hxv)).continuousWithinAt
    dTopology := .deltaGenerated X
    isOpen_iff_preimages_plots := isOpen_deltaGenerated_iff.trans <|
      forall_congr' fun n => ⟨fun h p hp => h ⟨p,hp⟩,fun h p => h p p.2⟩ }

/-- The D-topology of the continuous diffeology is the delta-generification of the
  original topology. -/
lemma dTop_continuousDiffeology {X : Type u} [TopologicalSpace X] :
    DTop[continuousDiffeology X] = .deltaGenerated X :=
  rfl

/-- For delta-generated spaces, the D-topology of the continuous diffeology is the
  topology itself. -/
lemma dTop_continuousDiffeology_eq_self {X : Type u} [t : TopologicalSpace X]
    [DeltaGeneratedSpace X] : DTop[continuousDiffeology X] = t :=
  dTop_continuousDiffeology.trans eq_deltaGenerated.symm

/-- Type synonym to get equipped with the continuous diffeology. -/
def withContinuousDiffeology (X : Type u) [TopologicalSpace X] := X

instance (X : Type u) [TopologicalSpace X] : DiffeologicalSpace (withContinuousDiffeology X) :=
  continuousDiffeology X

/-- Every continuous map is smooth with respect to the continuous diffeologies. -/
lemma Continuous.dsmooth {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) : DSmooth[continuousDiffeology X,continuousDiffeology Y] f :=
  fun _ _ hp => hf.comp hp

/-- Every continuous map into a space carrying the continuous diffeology is smooth. -/
lemma Continuous.dsmooth' {X Y : Type u} {dX : DiffeologicalSpace X} {tY : TopologicalSpace Y}
    {f : X → Y} (hf : Continuous[DTop,_] f) : DSmooth[_,continuousDiffeology Y] f := by
  let _ : TopologicalSpace X := DTop; exact fun n p hp => hf.comp hp.continuous
