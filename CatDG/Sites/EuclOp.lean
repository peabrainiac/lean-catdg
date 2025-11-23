import CatDG.Sites.CartSp

/-!
# The site `EuclOp` of open subsets of ℝⁿ

This file defines the category `EuclOp` of open subsets of the cartesian spaces ℝⁿ and smooth maps
between them and equips it with the good open cover coverage. This site is of relevance because
it is one of several sites on which concrete sheaves correspond exactly to diffeological spaces.

## Main definitions / results:
* `EuclOp`: the category of open subsets of euclidean spaces and smooth maps between them
* `EuclOp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `EuclOp` is a concrete subcanonical site
* `CartSp.toEuclOp`: the fully faithful embedding of `CartSp` into `EuclOp`
* `CartSp.toEuclOp` exhibits `CartSp` as a dense sub-site of `EuclOp`

## TODO
* Show that `EuclOp` has all finite products
* Show that that `CartSp.toEuclOp` preserves finite products
* Switch from `HasForget` to the new `ConcreteCategory` design
* Use `Presieve.IsJointlySurjective` more (currently runs into problems regarding which `FunLike`
  instances are used)
* Generalise `EuclOp` to take a smoothness parameter in `WithTop ℕ∞`
-/

universe u

open CategoryTheory Limits Sheaf TopologicalSpace Set

def EuclOp := (n : ℕ) × Opens (EuclideanSpace ℝ (Fin n))

namespace EuclOp

instance : CoeSort EuclOp Type where
  coe u := u.2

noncomputable instance : SmallCategory EuclOp where
  Hom := fun u v ↦ DSmoothMap u v
  id := fun n ↦ DSmoothMap.id _
  comp := fun f g ↦ g.comp f

instance : HasForget EuclOp where
  forget := { obj := fun u ↦ u, map := fun f ↦ f.1 }
  forget_faithful := { map_injective := fun {_ _} ↦ DSmoothMap.coe_injective }

instance instFunLike (u v : EuclOp) : FunLike (u ⟶ v) u v where
  coe f := DFunLike.coe (F := DSmoothMap _ _) f
  coe_injective' := DFunLike.coe_injective (F := DSmoothMap _ _)

@[simp]
theorem id_app (u : EuclOp) (x : u) : (𝟙 u : u ⟶ u) x = x := rfl

@[simp]
theorem comp_app {u v w : EuclOp} (f : u ⟶ v) (g : v ⟶ w) (x : u) :
    (f ≫ g : u → w) x = g (f x) := rfl

/-- The open cover coverage on `EuclOp`, consisting of all coverings by open smooth embeddings.
Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
used instead. -/
def openCoverCoverage : Coverage EuclOp where
  coverings u := {s | (∀ (v : _) (f : v ⟶ u), s f → IsOpenInduction f.1) ∧
    ⋃ (v : EuclOp) (f ∈ s (Y := v)), range f.1 = univ}
  pullback u v g s hs := by
    use fun k ↦ {f | (∃ (k : _) (f' : k ⟶ u), s f' ∧ range (g.1 ∘ f.1) ⊆ range f'.1)
      ∧ IsOpenInduction f}
    refine ⟨⟨fun k f hf ↦ hf.2, ?_⟩, ?_⟩
    · refine iUnion_eq_univ_iff.2 fun x ↦ ?_
      let ⟨w,hw⟩ := iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := mem_iUnion₂.1 hw
      have h := v.2.2.isOpenMap_subtype_val _
        ((hs.1 _ _ hf).isOpen_range'.preimage g.2.continuous')
      use ⟨_, _, h⟩
      refine mem_iUnion₂.2 ⟨⟨_, dsmooth_inclusion (Subtype.coe_image_subset _ _)⟩, ?_⟩
      refine ⟨⟨⟨w, f, hf, ?_⟩, ?_⟩, ?_⟩
      · simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe]
        rw [range_comp, range_inclusion]
        convert image_preimage_subset _ _; ext x
        rw [mem_setOf_eq, Subtype.val_injective.mem_set_image]
      · exact h.isOpenInduction_inclusion <| Subtype.coe_image_subset _ _
      · dsimp; rw [range_inclusion]; exact ⟨_, hgx, rfl⟩
    · intro k f ⟨⟨k',f',hf'⟩,_⟩; use k'
      let f'' := (DDiffeomorph.ofIsInduction (hs.1 k' f' hf'.1).1)
      use ⟨_,(f''.dsmooth_invFun.comp <|
        (f ≫ g).2.subtype_mk (fun x ↦ hf'.2 (mem_range_self x)))⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      simp_rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; exact congrArg Subtype.val <| f''.apply_symm_apply _

/-- The open cover grothendieck topology on `EuclOp`. -/
def openCoverTopology : GrothendieckTopology EuclOp :=
  openCoverCoverage.toGrothendieck

/-- A sieve belongs to `EuclOp.openCoverTopology` iff it contains a presieve from
`EuclOp.openCoverCoverage`. -/
lemma openCoverTopology.mem_sieves_iff {n : EuclOp} {s : Sieve n} :
    s ∈ openCoverTopology n ↔ ∃ r, r ≤ s.arrows ∧ r ∈ openCoverCoverage n := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr⟩ ↦ Coverage.mem_toGrothendieck_sieves_of_superset _ hr.1 hr.2⟩
  induction h with
  | of n s hs =>
    exact ⟨s, Sieve.le_generate s, hs⟩
  | top n =>
    refine ⟨fun k f ↦ IsOpenInduction f, le_top, fun k f hf ↦ hf, ?_⟩
    exact univ_subset_iff.1 <| subset_iUnion_of_subset n <|
        subset_iUnion₂_of_subset (𝟙 n) isOpenInduction_id (range_id.symm.subset)
  | transitive n s r _ _ hs hr =>
    let ⟨s', hs'⟩ := hs
    refine ⟨fun k f ↦ r f ∧ IsOpenInduction f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, ?_⟩
    rw [← univ_subset_iff, ← hs'.2.2]
    refine iUnion_subset fun m ↦ iUnion₂_subset fun f hf ↦ ?_
    let ⟨r', hr'⟩ := hr (hs'.1 _ hf)
    simp_rw [← image_univ, ← hr'.2.2, image_iUnion]
    refine iUnion_subset fun k ↦ iUnion₂_subset fun g hg ↦ ?_
    refine subset_iUnion_of_subset k <| subset_iUnion₂_of_subset (g ≫ f) ⟨?_, ?_⟩ ?_
    · exact hr'.1 _ hg
    · exact (hs'.2.1 _ _ hf).comp (hr'.2.1 _ _ hg)
    · rw [← range_comp, image_univ]; rfl

/- A sieve belongs to `EuclOp.openCoverTopology` iff the open inductions in it are jointly
surjective. -/
lemma openCoverTopology.mem_sieves_iff' {n : EuclOp} {s : Sieve n} :
    s ∈ openCoverTopology n ↔
    ⋃ (m) (f : m ⟶ n) (_ : s f ∧ IsOpenInduction f), range f = univ := by
  refine mem_sieves_iff.trans ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← univ_subset_iff, ← hr.2.2]
    exact iUnion_subset fun m ↦ iUnion₂_subset fun f hf ↦ subset_iUnion_of_subset m <|
      subset_iUnion₂_of_subset f ⟨hr.1 _ hf, hr.2.1 m f hf⟩ subset_rfl
  · exact ⟨fun m f ↦ s f ∧ IsOpenInduction f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, h⟩

/-- `univ : Set (Eucl 0)` is terminal in `EuclOp`. -/
noncomputable def isTerminal0Top : IsTerminal (C := EuclOp) ⟨0, ⊤⟩ where
  lift s := DSmoothMap.const _ ⟨0, mem_univ _⟩
  uniq c f h := by
    ext x; exact Subsingleton.elim (α := univ (α := Eucl 0)) (f x) ⟨0, mem_univ _⟩

-- TODO: show more generally that `EuclOp` has finite products
instance : HasTerminal EuclOp := isTerminal0Top.hasTerminal

-- TODO: figure out how to get this from more general instances
noncomputable instance : Unique (⊤_ EuclOp) := by
  have : Unique ((forget EuclOp).obj ⟨0, ⊤⟩) :=
    uniqueOfSubsingleton (α := (univ (α := Eucl 0))) ⟨0, mem_univ _⟩
  exact ((forget _).mapIso (terminalIsTerminal.uniqueUpToIso isTerminal0Top)).toEquiv.unique

/-- `EuclOp` is a concrete site, in that it is concrete with elements corresponding to morphisms
from the terminal object and carries a topology consisting entirely of jointly surjective sieves. -/
noncomputable instance : openCoverTopology.IsConcreteSite where
  forgetNatIsoCoyoneda := NatIso.ofComponents fun u ↦
    (DSmoothMap.equivFnOfUnique (Y := u.2)).toIso.symm
  forgetNatIsoCoyoneda_apply := rfl
  isJointlySurjective_of_mem hs := by
    rw [openCoverTopology.mem_sieves_iff] at hs
    obtain ⟨r, hr⟩ := hs
    exact .mono hr.1 <| Presieve.isJointlySurjective_iff_iUnion_range_eq_univ.2 hr.2.2

open GrothendieckTopology.IsConcreteSite in
/-- `EuclOp` is a subcanonical site, i.e. all representable presheaves on it are sheaves. -/
instance : openCoverTopology.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun n m s hs ↦
    (isSeparated_yoneda_obj _ n s hs).isSheafFor fun f hf ↦ ?_
  let hs' := hs; simp_rw [openCoverTopology.mem_sieves_iff', eq_univ_iff_forall, mem_iUnion] at hs'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x
    exact (show ⊤_ EuclOp ⟶ n from f _ <| from_terminal_mem_of_mem _ hs (.const _ x)) default
  · refine dsmooth_iff_locally_dsmooth.2 fun x ↦ ?_
    let ⟨k, g, hg, hx⟩ := hs' x
    refine ⟨_, hg.2.isOpen_range, hx, ?_⟩
    rw [← hg.2.dsmooth_comp_iff_dsmooth_restrict]
    convert (f g hg.1).dsmooth; ext1 x'
    specialize hf (𝟙 (⊤_ _)) (Y₂ := k) (DSmoothMap.const _ x')
      (from_terminal_mem_of_mem _ hs (.const _ (g x'))) hg.1 rfl
    exact congrFun (congrArg DSmoothMap.toFun hf) (default : ⊤_ EuclOp)
  · intro k g hg; dsimp; ext1 x
    specialize hf (𝟙 (⊤_ _)) (Y₂ := k) (DSmoothMap.const _ x)
      (from_terminal_mem_of_mem _ hs (.const _ (g x))) hg rfl
    exact congrFun (congrArg DSmoothMap.toFun hf) (default : ⊤_ EuclOp)

end EuclOp

section CartSpToEuclOp

/-- The embedding of `CartSp` into `EuclOp`. -/
noncomputable def CartSp.toEuclOp : CartSp ⥤ EuclOp where
  obj n := ⟨n, ⊤⟩
  map f := ⟨_, f.2.restrict (mapsTo_univ f univ)⟩

/-- Open subsets of cartesian spaces can be covered with cartesian spaces. -/
instance : CartSp.toEuclOp.IsCoverDense EuclOp.openCoverTopology := by
  constructor; intro u
  refine EuclOp.openCoverCoverage.mem_toGrothendieck_sieves_of_superset (R := ?_) ?_ ?_
  · exact fun {v} f ↦ v.2.1 = univ ∧ IsOpenInduction f.1
  · intro v f hf
    refine ⟨⟨v.1, ⟨_, dsmooth_id.restrict (mapsTo_univ _ _)⟩, ?_, ?_⟩⟩
    · let e : CartSp.toEuclOp.obj v.1 ⟶ v :=
        ⟨_, dsmooth_id.restrict (by convert mapsTo_univ _ _; exact hf.1)⟩
      exact e ≫ f
    · ext x; rfl
  · refine ⟨fun v f hf ↦ hf.2, iUnion_eq_univ_iff.2 fun x ↦ ?_⟩
    use ⟨u.1, ⊤⟩; apply mem_iUnion₂.2
    let ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1 u.2.2 x.1 x.2
    let e := (DDiffeomorph.Set.univ _).trans (DDiffeomorph.univBall x.1 hε)
    use ⟨_, (dsmooth_inclusion hxε).comp e.dsmooth⟩
    refine ⟨⟨rfl, ?_⟩, ?_⟩
    · exact (Metric.isOpen_ball.isOpenInduction_inclusion' hxε).comp e.isOpenInduction
    · rw [range_comp, e.surjective.range_eq, image_univ]
      use ⟨x.1, Metric.mem_ball_self hε⟩; rfl

instance CartSp.toEuclOp_fullyFaithful : CartSp.toEuclOp.FullyFaithful where
  preimage {n m} f := by
    exact ⟨_, (dsmooth_subtype_val.comp f.2).comp (dsmooth_id.subtype_mk (mem_univ))⟩

instance : CartSp.toEuclOp.Full := CartSp.toEuclOp_fullyFaithful.full

instance : CartSp.toEuclOp.Faithful := CartSp.toEuclOp_fullyFaithful.faithful

/-- `CartSp.toEuclOp` exhibits `CartSp` as a dense sub-site of `EuclOp` with respect to the
open cover topologies.
In particular, the sheaf topoi of the two sites are equivalent via `IsDenseSubsite.sheafEquiv`. -/
instance : CartSp.toEuclOp.IsDenseSubsite
    CartSp.openCoverTopology EuclOp.openCoverTopology where
  functorPushforward_mem_iff {n} s := by
    rw [CartSp.openCoverTopology.mem_sieves_iff', EuclOp.openCoverTopology.mem_sieves_iff']
    refine (DDiffeomorph.Set.univ (Eucl n)).injective.image_injective.eq_iff.symm.trans ?_
    rw [image_univ, (DDiffeomorph.Set.univ (Eucl n)).surjective.range_eq]
    simp_rw [image_iUnion, ← range_comp]
    refine Eq.congr_left (subset_antisymm ?_ ?_)
    · refine iUnion_subset fun u ↦ iUnion₂_subset fun f hf ↦ ?_
      obtain ⟨m, g, h, hg, rfl⟩ := hf.1; replace hf := hf.2
      refine range_subset_iff.2 fun x ↦ ?_
      let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 u.2.2 x.1 x.2
      let i : DSmoothMap _ _ := ⟨_, dsmooth_inclusion hε'⟩
      let e := DDiffeomorph.univBall x.1 hε
      refine mem_iUnion_of_mem _ <| mem_iUnion₂_of_mem
        (i := ⟨_, (DDiffeomorph.Set.univ _).dsmooth.comp <|
          h.dsmooth.comp <| i.dsmooth.comp e.dsmooth⟩ ≫ g) ⟨?_, ?_⟩ ?_
      · exact s.downward_closed hg _
      · exact (DDiffeomorph.Set.univ _).isOpenInduction.comp <| hf.comp <|
          (Metric.isOpen_ball.isOpenInduction_inclusion hε').comp e.isOpenInduction
      use 0
      have h : i (e 0) = x := by ext1; simp_rw [← DDiffeomorph.coe_univBall_zero x.1 hε]; rfl
      simp_rw [← h]; rfl
    · refine iUnion_subset fun m ↦ iUnion₂_subset fun f hf ↦ ?_
      refine subset_iUnion_of_subset _ <| subset_iUnion₂_of_subset
        (CartSp.toEuclOp.map f) ⟨?_, ?_⟩ ?_
      · exact ⟨m, f, 𝟙 _, hf.1, (Category.id_comp _).symm⟩
      · exact hf.2.restrict isOpen_univ (mapsTo_univ _ _)
      · refine HasSubset.subset.trans_eq ?_
          (congrArg range (MapsTo.restrict_commutes _ _ _ (mapsTo_univ _ _)).symm)
        rw [range_comp, Subtype.range_val, ← image_univ]; rfl

end CartSpToEuclOp
