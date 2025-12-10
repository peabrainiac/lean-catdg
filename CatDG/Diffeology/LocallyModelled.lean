import CatDG.Diffeology.Constructions
import CatDG.Diffeology.DDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Locally Modelled Spaces
Diffeological space that are locally modelled on a family of other diffeological spaces.
This mainly functions are infrastructure for manifolds and orbifolds, setting up their
definitions and a few basic facts they have in common.
-/

open Topology

/-- A diffeological space is locally modelled by a family of diffeological spaces if each point
in it has a neighbourhood that's diffeomorphic to a space in the family. -/
class LocallyModelled {ι : Type*} (M : ι → Type*) [(i : ι) → DiffeologicalSpace (M i)]
    (X : Type*) [DiffeologicalSpace X] : Prop where
  locally_modelled : ∀ x : X, ∃ (u : Set X), IsOpen[DTop] u ∧ x ∈ u ∧
    ∃ (i : ι) (v : Set (M i)), IsOpen[DTop] v ∧ Nonempty (u ᵈ≃ v)

/-- A diffeological space is a manifold if it is locally modelled by R^n.
We do not require Hausdorffness or second-countability here. -/
abbrev IsDiffeologicalManifold (n : ℕ) (X : Type*) [DiffeologicalSpace X] :=
  LocallyModelled (fun _ : Unit ↦ Eucl n) X

/-- A diffeological space is a manifold with boundary if it is locally modelled by the
half-space H^n.
We do not require Hausdorffness or second-countability here. -/
abbrev IsManifoldWithBoundary (n : ℕ) [Zero (Fin n)] (X : Type*) [DiffeologicalSpace X] :=
  LocallyModelled (fun _ : Unit ↦ {x : Eucl n | 0 ≤ x 0}) X

/-- A diffeological space is an orbifold if it is locally modelled by quotients of R^n by finite
subgroups of GL(n). -/
abbrev IsOrbifold (n : ℕ) (X : Type*) [DiffeologicalSpace X] :=
  LocallyModelled (fun Γ : {Γ : Subgroup ((Eucl n) ≃ₗ[ℝ] (Eucl n)) | Finite Γ} ↦
    MulAction.orbitRel.Quotient Γ (Eucl n)) X

/-- Any D-open subset of a locally modelled space is locally modelled by the same family of
spaces. -/
protected theorem IsOpen.locallyModelled {X ι : Type*} [DiffeologicalSpace X] {M : ι → Type*}
    [(i : ι) → DiffeologicalSpace (M i)] (h : LocallyModelled M X) {u : Set X}
    (hu : IsOpen[DTop] u) : LocallyModelled M u :=
  ⟨fun x ↦ by
    let _ : TopologicalSpace X := DTop; let _ : (i : ι) → TopologicalSpace (M i) := fun _ ↦ DTop
    have : DTopCompatible X := ⟨rfl⟩; have : DTopCompatible u := hu.dTopCompatible
    have _ : (i : ι) → DTopCompatible (M i) := fun _ ↦ ⟨rfl⟩
    let ⟨v,hv,hxv,i,v',hv',⟨d⟩⟩ := h.locally_modelled x
    have := hv.dTopCompatible; have := hv'.dTopCompatible
    refine ⟨(↑) ⁻¹' v,?_,(by exact hxv),i,?_⟩
    · rw [dTop_eq u]; exact hv.preimage continuous_subtype_val
    have e : ((↑) ⁻¹' v : Set u) ᵈ≃ ((↑) ⁻¹' u : Set v) := by
      have e := DDiffeomorph.Set.nested ((↑) ⁻¹' v : Set u)
      have e' := DDiffeomorph.Set.nested ((↑) ⁻¹' u : Set v)
      rw [Subtype.image_preimage_val] at e e'; rw [Set.inter_comm] at e
      exact e.trans e'.symm
    have e' := (e.trans (d.restrict _)).trans (DDiffeomorph.Set.nested _)
    refine ⟨_,hv'.isOpenMap_subtype_val _ ?_,⟨e'⟩⟩
    exact ((dTop_eq X ▸ hu).preimage continuous_subtype_val).preimage d.symm.dsmooth.continuous'⟩

/-- Any D-open subset of a diffeological manifold is a diffeological manifold. -/
protected theorem IsOpen.isDiffeologicalManifold {X : Type*} [DiffeologicalSpace X] {n : ℕ}
    (h : IsDiffeologicalManifold n X) {u : Set X} (hu : IsOpen[DTop] u) :
    IsDiffeologicalManifold n u :=
  hu.locallyModelled h

/-- Any D-open subset of a diffeological manifold with boundary is a diffeological
manifold with boundary. -/
protected theorem IsOpen.isManifoldWithBoundary {X : Type*} [DiffeologicalSpace X] {n : ℕ}
    [Zero (Fin n)] (h : IsManifoldWithBoundary n X) {u : Set X} (hu : IsOpen[DTop] u) :
    IsManifoldWithBoundary n u := hu.locallyModelled h

/-- Any D-open subset of a diffeological orbifold is a diffeological orbifold. -/
protected theorem IsOpen.isOrbifold {X : Type*} [DiffeologicalSpace X] {n : ℕ}
    [Zero (Fin n)] (h : IsOrbifold n X) {u : Set X} (hu : IsOpen[DTop] u) :
    IsOrbifold n u := hu.locallyModelled h

/-- `Eucl n` is a diffeological manifold. -/
instance {n : ℕ} : IsDiffeologicalManifold n (Eucl n) :=
  ⟨fun x ↦ ⟨_,isOpen_univ,Set.mem_univ x,(),Set.univ,isOpen_univ,⟨DDiffeomorph.refl _⟩⟩⟩

/-- Any diffeological manifold is also a diffeological manifold with boundary. -/
instance {n : ℕ} {X : Type*} [Zero (Fin n)] [DiffeologicalSpace X]
    [hm : IsDiffeologicalManifold n X] : IsManifoldWithBoundary n X := ⟨fun x ↦ by
  let ⟨u,hu,hxu,i,v,hv,⟨d⟩⟩ := hm.locally_modelled x
  -- TODO: requires diffeomorphism of R^n to a ball in H^n
  sorry⟩

set_option synthInstance.maxHeartbeats 40000 in
/-- Any diffeological manifold is also a diffeological orbifold. -/
instance {n : ℕ} {X : Type*} [DiffeologicalSpace X] [hm : IsDiffeologicalManifold n X] :
    IsOrbifold n X := ⟨fun x ↦ by
  let ⟨u,hu,hxu,_,v,hv,⟨d⟩⟩ := hm.locally_modelled x
  refine ⟨u,hu,hxu,⟨⊥,Set.mem_setOf_eq ▸ inferInstance⟩,?_⟩
  -- TODO: generalise, move somewhere else
  have h : MulAction.orbitRel (⊥ : Subgroup ((Eucl n) ≃ₗ[ℝ] (Eucl n))) (Eucl n) = ⊥ := by
    ext a b; dsimp; rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff]
    refine ⟨fun ⟨g,hg⟩ ↦ hg ▸ ?_,fun h ↦ ⟨1,by rw [h,one_smul]⟩⟩
    rw [Unique.eq_default g,unique_one,one_smul]
  dsimp [MulAction.orbitRel.Quotient]; rw [h]
  have e := d.trans ((DDiffeomorph.quotient_bot (Eucl n)).restrictPreimage v).symm
  refine ⟨(Quotient.lift id fun a b ↦ id) ⁻¹' v,?_,⟨e⟩⟩
  exact @IsOpen.preimage _ _ DTop DTop _ (dsmooth_id.quotient_lift _).continuous _ hv⟩

/-- Spaces that are modelled on locally compact spaces are locally compact. -/
protected theorem LocallyModelled.locallyCompactSpace {X ι : Type*} [DiffeologicalSpace X]
    {M : ι → Type*} [(i : ι) → TopologicalSpace (M i)] [(i : ι) → DiffeologicalSpace (M i)]
    [(i : ι) → DTopCompatible (M i)] [(i : ι) → LocallyCompactSpace (M i)]
    (h : LocallyModelled M X) : @LocallyCompactSpace X DTop := by
  let _ : TopologicalSpace X := DTop; have : DTopCompatible X := ⟨rfl⟩
  constructor; intro x s hs
  let ⟨u, hu, hxu, i, v, hv, ⟨d⟩⟩ := h.locally_modelled x; rw [dTop_eq] at hv
  have := hu.dTopCompatible; have := hv.dTopCompatible
  have := d.toHomeomorph'.locallyCompactSpace_iff.mpr hv.locallyCompactSpace
  let ⟨t, ht, hts, ht'⟩ := local_compact_nhds <|
    (mem_nhds_subtype u ⟨x, hxu⟩ _).mpr ⟨s, hs, subset_rfl⟩
  refine ⟨(↑) '' t, ?_, by simp [hts], ht'.image continuous_subtype_val⟩
  exact hu.isOpenMap_subtype_val.image_mem_nhds ht

/-- The quotient spaces that orbifolds are modelled on are locally compact. -/
instance {n : ℕ} {Γ : {Γ : Subgroup ((Eucl n) ≃ₗ[ℝ] (Eucl n)) | Finite Γ}} :
    LocallyCompactSpace (MulAction.orbitRel.Quotient Γ (Eucl n)) := by
  sorry

/-- Orbifolds are locally compact. Not an instance because lean can't infer typeclasses that
don't depend on `n` from ones that do.
TODO: solve by allowing orbifolds of mixed dimension? -/
protected theorem IsOrbifold.locallyCompactSpace {X : Type*} [TopologicalSpace X]
    [DiffeologicalSpace X] [DTopCompatible X] {n : ℕ} [hX : IsOrbifold n X] :
    LocallyCompactSpace X := by
  exact (dTop_eq X) ▸ LocallyModelled.locallyCompactSpace hX
