import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Sites.Canonical
import CatDG.Cohesive.CohesiveSite
import CatDG.Diffeology.Hadamard
import CatDG.ForMathlib.ConcreteSite

/-!
# CartSp and EuclOp

This file defines the sites `CartSp` and `EuclOp` of cartesian spaces resp. open subsets of
cartesian spaces and smooth maps, both with the good open cover coverage. These
sites are of relevance because concrete sheaves on them correspond to diffeological spaces,
although sheaves on them are studied not in this file but in `CatDG.Diffeology.SmoothSp`.

See https://ncatlab.org/nlab/show/CartSp.

Note that with the current implementation, this could not be used to *define*
diffeological spaces - it already uses diffeology in the definition of
`CartSp.openCoverCoverage`. The reason is that smooth embeddings are apparently not yet
implemented in mathlib, so diffeological inductions are used instead.

Main definitions / results:
* `CartSp`: the category of euclidean spaces and smooth maps between them
* `CartSp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `CartSp` has all finite products
* `CartSp` is a concrete, cohesive and subcanonical site
* `EuclOp`: the category of open subsets of euclidean spaces and smooth maps between them
* `EuclOp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `EuclOp` is a concrete subcanonical site
* `CartSp.toEuclOp`: the fully faithful embedding of `CartSp` into `EuclOp`
* `CartSp.toEuclOp` exhibits `CartSp` as a dense sub-site of `EuclOp`
* `CartSp.toCommAlgCatOp`: the fully faithful embedding of `CartSp` into `(CommAlgCat ℝ)ᵒᵖ`

## TODO
* Show that `EuclOp` has all finite products
* Show that that `CartSp.toEuclOp` preserves finite products
* Switch from `HasForget` to the new `ConcreteCategory` design
* Use `Presieve.IsJointlySurjective` more (currently runs into problems regarding which `FunLike`
  instances are used)
* Generalise `CartSp` to take a smoothness parameter in `ℕ∞`
* Generalise `EuclOp` to take a smoothness parameter in `WithTop ℕ∞`
* General results about concrete sites
-/

universe u

open CategoryTheory Limits Sheaf TopologicalSpace Set

def CartSp := ℕ

namespace CartSp

instance : CoeSort CartSp Type where
  coe n := EuclideanSpace ℝ (Fin n)

instance (n : ℕ) : OfNat CartSp n where
  ofNat := n

noncomputable instance : SmallCategory CartSp where
  Hom := fun n m ↦ DSmoothMap n m
  id := fun n ↦ DSmoothMap.id _
  comp := fun f g ↦ g.comp f

instance : HasForget CartSp where
  forget := { obj := fun n ↦ n, map := fun f ↦ f.1 }
  forget_faithful := { map_injective := fun {_ _} ↦ DSmoothMap.coe_injective }

instance instFunLike (n m : CartSp) : FunLike (n ⟶ m) n m where
  coe f := DFunLike.coe (F := DSmoothMap _ _) f
  coe_injective' := DFunLike.coe_injective (F := DSmoothMap _ _)

@[simp]
theorem id_app (n : CartSp) (x : n) : (𝟙 n : n ⟶ n) x = x := rfl

@[simp]
theorem comp_app {n m k : CartSp} (f : n ⟶ m) (g : m ⟶ k) (x : n) :
    (f ≫ g : n → k) x = g (f x) := rfl

/-- The open cover coverage on `CartSp`, consisting of all coverings by open smooth embeddings.
Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
used instead. -/
def openCoverCoverage : Coverage CartSp where
  coverings n := {s | (∀ (m : _) (f : m ⟶ n), s f → IsOpenInduction f) ∧
    ⋃ (m : CartSp) (f ∈ s (Y := m)), range f.1 = univ}
  pullback n m g s hs := by
    use fun k ↦ {f | (∃ (k : _) (f' : k ⟶ n), s f' ∧ range (g.1 ∘ f.1) ⊆ range f'.1)
      ∧ IsOpenInduction f}
    refine ⟨⟨fun k f hf ↦ hf.2, ?_⟩, ?_⟩
    · refine iUnion_eq_univ_iff.2 fun x ↦ ?_
      let ⟨k,hk⟩ := iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := mem_iUnion₂.1 hk
      refine ⟨m, mem_iUnion₂.2 ?_⟩
      let ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1
        ((hs.1 k f hf).isOpen_range.preimage g.2.continuous) x hgx
      let e := (DDiffeomorph.univBall x hε)
      use ⟨_, dsmooth_subtype_val.comp e.dsmooth⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · refine ⟨k, f, hf, _root_.subset_trans ?_ (image_subset_iff.2 hxε)⟩
        simp_rw [range_comp]; apply image_mono; simpa using subset_rfl
      · refine (IsOpen.isOpenInduction_subtype_val' Metric.isOpen_ball).comp e.isOpenInduction
      · change x ∈ range (Subtype.val ∘ e.toEquiv)
        rw [e.toEquiv.surjective.range_comp]; simp [hε]
    · intro k f ⟨⟨k',f',hf'⟩,_⟩; use k'
      let f'' := (DDiffeomorph.ofIsInduction (hs.1 k' f' hf'.1).1)
      use ⟨_,(f''.dsmooth_invFun.comp <|
        (f ≫ g).2.subtype_mk (fun x ↦ hf'.2 (mem_range_self x)))⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      simp_rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; exact congrArg Subtype.val <| f''.apply_symm_apply _

/-- The open cover grothendieck topology on `CartSp`. -/
def openCoverTopology : GrothendieckTopology CartSp :=
  openCoverCoverage.toGrothendieck

/-- A sieve belongs to `CartSp.openCoverTopology` iff it contains a presieve from
`CartSp.openCoverCoverage`. -/
lemma openCoverTopology.mem_sieves_iff {n : CartSp} {s : Sieve n} :
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

/- A sieve belongs to `CartSp.openCoverTopology` iff the open inductions in it are jointly
surjective. -/
lemma openCoverTopology.mem_sieves_iff' {n : CartSp} {s : Sieve n} :
    s ∈ openCoverTopology n ↔
    ⋃ (m) (f : m ⟶ n) (_ : s f ∧ IsOpenInduction f), range f = univ := by
  refine mem_sieves_iff.trans ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← univ_subset_iff, ← hr.2.2]
    exact iUnion_subset fun m ↦ iUnion₂_subset fun f hf ↦ subset_iUnion_of_subset m <|
      subset_iUnion₂_of_subset f ⟨hr.1 _ hf, hr.2.1 m f hf⟩ subset_rfl
  · exact ⟨fun m f ↦ s f ∧ IsOpenInduction f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, h⟩

/-- The `0`-dimensional cartesian space is terminal in `CartSp`. -/
noncomputable def isTerminal0 : IsTerminal (0 : CartSp) where
  lift s := DSmoothMap.const _ 0
  uniq c f h := by ext x; exact Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) (f x) 0

/-- The first projection realising `EuclideanSpace ℝ (Fin (n + m))` as the product of
`EuclideanSpace ℝ n` and `EuclideanSpace ℝ m`. -/
noncomputable abbrev prodFst {n m : CartSp} :
    @Quiver.Hom CartSp _ (@HAdd.hAdd ℕ ℕ _ _ n m) n :=
  DSmoothMap.fst.comp EuclideanSpace.finAddEquivProd.toDDiffeomorph.toDSmoothMap

/-- The second projection realising `EuclideanSpace ℝ (Fin (n + m))` as the product of
`EuclideanSpace ℝ n` and `EuclideanSpace ℝ m`. -/
noncomputable abbrev prodSnd {n m : CartSp} :
    @Quiver.Hom CartSp _ (@HAdd.hAdd ℕ ℕ _ _ n m) m :=
  DSmoothMap.snd.comp EuclideanSpace.finAddEquivProd.toDDiffeomorph.toDSmoothMap

/-- The explicit binary fan of `EuclideanSpace ℝ n` and `EuclideanSpace ℝ m` given by
`EuclideanSpace ℝ (Fin (n + m))`. -/
noncomputable def prodBinaryFan (n m : CartSp) : BinaryFan n m :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit. -/
noncomputable def prodBinaryFanIsLimit (n m : CartSp) : IsLimit (prodBinaryFan n m) where
  lift c := EuclideanSpace.finAddEquivProd.toDDiffeomorph.symm.toDSmoothMap.comp <|
    DSmoothMap.prodMk (BinaryFan.fst c) (BinaryFan.snd c)
  fac := by
    rintro c (_ | _) <;> dsimp [prodBinaryFan, prodFst]
    all_goals ext (x : EuclideanSpace _ _)
    -- TODO: figure out how to better deal with simp-breaking situations like this
    all_goals rw [CategoryTheory.comp_apply]
    · exact congrArg Prod.fst (EuclideanSpace.finAddEquivProd.toDDiffeomorph.apply_symm_apply _)
    · exact congrArg Prod.snd (EuclideanSpace.finAddEquivProd.toDDiffeomorph.apply_symm_apply _)
  uniq c f h := by
    ext x
    change _ = EuclideanSpace.finAddEquivProd.toDDiffeomorph.toEquiv.symm _
    rw [Equiv.eq_symm_apply]
    refine Prod.ext ?_ ?_
    · simpa using congrFun (congrArg DSmoothMap.toFun (h { as := WalkingPair.left })) x
    · simpa using congrFun (congrArg DSmoothMap.toFun (h { as := WalkingPair.right })) x

instance : HasFiniteProducts CartSp := by
  refine @hasFiniteProducts_of_has_binary_and_terminal _ _ ?_ isTerminal0.hasTerminal
  exact @hasBinaryProducts_of_hasLimit_pair _ _ ⟨⟨_, prodBinaryFanIsLimit _ _⟩⟩

-- TODO: figure out how to get this from more general instances
noncomputable instance : Unique (⊤_ CartSp) := by
  have : Unique ((forget CartSp).obj 0) := inferInstanceAs (Unique (Eucl 0))
  exact ((forget _).mapIso (terminalIsTerminal.uniqueUpToIso isTerminal0)).toEquiv.unique

/-- `CartSp` is a locally connected site, roughly meaning that each of its objects is connected.
Note that this is different from `EuclOp`, which also contains disconnected open sets and thus isn't
locally connected. -/
instance : openCoverTopology.IsLocallyConnectedSite where
  isConnected_of_mem {n} s hs := by
    simp_rw [openCoverTopology.mem_sieves_iff', eq_univ_iff_forall, mem_iUnion] at hs
    have hs' : ∀ f : ⊤_ _ ⟶ n, s.arrows f := fun f ↦ by
      let ⟨m, g, hg, x, hx⟩ := hs (f 0)
      convert s.downward_closed (Z := ⊤_ _) hg.1 (DSmoothMap.const _ x)
      ext _; exact (congrArg _ (Subsingleton.allEq (α := ⊤_ CartSp) _ _)).trans hx.symm
    have _ : Nonempty s.arrows.category := ⟨.mk (Y := ⊤_ _) (DSmoothMap.const _ 0), hs' _⟩
    refine .of_constant_of_preserves_morphisms fun {α} F hF ↦ ?_
    let F' : n → α := fun x ↦ F ⟨.mk (DSmoothMap.const _ x), hs' _⟩
    have hF' : IsLocallyConstant F' := by
      refine (IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_
      let ⟨m, f, hf, y, hy⟩ := hs x
      refine ⟨range f, hf.2.isOpen_range, ⟨y, hy⟩, fun x' ⟨y', hy'⟩ ↦ ?_⟩
      rw [← hy, ← hy']
      exact (@hF ⟨.mk (DSmoothMap.const _ (f y')), hs' _⟩ ⟨.mk f, hf.1⟩
        (Over.homMk (DSmoothMap.const _ y'))).trans
        (@hF ⟨.mk (DSmoothMap.const _ (f y)), hs' _⟩ ⟨.mk f, hf.1⟩
          (Over.homMk (DSmoothMap.const _ y))).symm
    exact fun f g ↦ (@hF ⟨.mk (DSmoothMap.const _ (f.1.hom 0)), hs' _⟩ ⟨.mk f.1.hom, f.2⟩
      (Over.homMk (DSmoothMap.const _ 0))).symm.trans <|
      (IsLocallyConstant.iff_is_const.1 hF' _ _).trans <|
      @hF ⟨.mk (DSmoothMap.const _ (g.1.hom 0)), hs' _⟩ ⟨.mk g.1.hom, g.2⟩
        (Over.homMk (DSmoothMap.const _ 0))

/-- `CartSp` is a cohesive site (i.e. in particular locally connected and local, but with a few more
properties). From this it follows that the sheaves on it form a cohesive topos.
Note that `EuclOp` (defined below) is *not* a cohesive site, as it isn't locally connected. Sheaves
on it form a cohesive topos too nonetheless, simply because the sheaf topoi on `EuclOp` and `CartSp`
are equivalent. -/
instance : openCoverTopology.IsCohesiveSite where
  nonempty_fromTerminal := ⟨DSmoothMap.const _ 0⟩

/-- `CartSp` is a concrete site, in that it is concrete with elements corresponding to morphisms
from the terminal object and carries a topology consisting entirely of jointly surjective sieves. -/
noncomputable instance : openCoverTopology.IsConcreteSite where
  forgetNatIsoCoyoneda := NatIso.ofComponents fun n ↦
    (DSmoothMap.equivFnOfUnique (Y := Eucl n)).toIso.symm
  forgetNatIsoCoyoneda_apply := rfl
  isJointlySurjective_of_mem hs := by
    rw [openCoverTopology.mem_sieves_iff] at hs
    obtain ⟨r, hr⟩ := hs
    exact .mono hr.1 <| Presieve.isJointlySurjective_iff_iUnion_range_eq_univ.2 hr.2.2

open GrothendieckTopology.IsConcreteSite in
/-- `CartSp` is a subcanonical site, i.e. all representable presheaves on it are sheaves. -/
instance : openCoverTopology.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun n m s hs ↦
    (isSeparated_yoneda_obj _ n s hs).isSheafFor fun f hf ↦ ?_
  let hs' := hs; simp_rw [openCoverTopology.mem_sieves_iff', eq_univ_iff_forall, mem_iUnion] at hs'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x
    exact (show ⊤_ CartSp ⟶ n from f _ <| from_terminal_mem_of_mem _ hs (.const _ x)) default
  · refine dsmooth_iff_locally_dsmooth.2 fun x ↦ ?_
    let ⟨k, g, hg, hx⟩ := hs' x
    refine ⟨_, hg.2.isOpen_range, hx, ?_⟩
    rw [← hg.2.dsmooth_comp_iff_dsmooth_restrict]
    convert (f g hg.1).dsmooth; ext1 x'
    specialize hf (𝟙 (⊤_ _)) (Y₂ := k) (DSmoothMap.const _ x')
      (from_terminal_mem_of_mem _ hs (.const _ (g x'))) hg.1 rfl
    exact congrFun (congrArg DSmoothMap.toFun hf) (default : ⊤_ CartSp)
  · intro k g hg; dsimp; ext1 x
    specialize hf (𝟙 (⊤_ _)) (Y₂ := k) (DSmoothMap.const _ x)
      (from_terminal_mem_of_mem _ hs (.const _ (g x))) hg rfl
    exact congrFun (congrArg DSmoothMap.toFun hf) (default : ⊤_ CartSp)

end CartSp

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

/-!
### Embeddings into other categories
TODO: split this off into some other file, to reduce the imports of this file
-/

section Embeddings

/-- The embedding of `CartSp` into the opposite category of `ℝ`-algebras, sending each space `X`
to the algebra of smooth maps `X → ℝ`. -/
@[simps!]
noncomputable def CartSp.toCommAlgCatOp : CartSp ⥤ (CommAlgCat ℝ)ᵒᵖ where
  obj X := .op (.of ℝ (DSmoothMap X ℝ))
  map {n m} f := .op <| CommAlgCat.ofHom f.compRightAlgHom

/-- The embedding of `CartSp` into `(CommAlgCat ℝ)ᵒᵖ` is fully faithful. Given a homomorphism
`f : DSmoothMap (Eucl m) ℝ →ₐ[ℝ] DSmoothMap (Eucl n) ℝ` of `ℝ`-algebras, a corresponding smooth
function `Eucl n → Eucl m` can be constructed by transporting the coordinate functions
`Eucl m → ℝ` along `f`. -/
noncomputable def CartSp.toCommAlgCatOpFullyFaithful : CartSp.toCommAlgCatOp.FullyFaithful where
  preimage {n m} f := by
    let f' (k : Fin m) : DSmoothMap _ _ := f.unop (EuclideanSpace.proj k).toDSmoothMap
    exact (∑ k, f' k • DSmoothMap.const (Eucl n) (EuclideanSpace.single k (1 : ℝ)):)
  map_preimage {n m} f := by
    let f' : DSmoothMap _ _ →ₐ[ℝ] DSmoothMap _ _ := f.unop.hom
    refine Quiver.Hom.unop_inj ?_
    ext1; ext1 (g : DSmoothMap _ _)
    dsimp [DSmoothMap.compRightAlgHom, DSmoothMap.compRightRingHom]
    ext x
    let x' := ∑ k, (f' (EuclideanSpace.proj k).toDSmoothMap) x • EuclideanSpace.single k (1 : ℝ)
    simp only [DSmoothMap.comp_apply, DSmoothMap.coe_sum, DSmoothMap.coe_smul',
      DSmoothMap.coe_const, Finset.sum_apply, Pi.smul_apply', Function.const_apply]
    change g x' = (f' g) x
    nth_rewrite 2 [g.eq_add_sum_hadamardFun x' (EuclideanSpace.basisFun (Fin m) ℝ).toBasis]
    have h c : (f' (DSmoothMap.const (EuclideanSpace ℝ (Fin m)) c)) x = c :=
      congrFun (congrArg DSmoothMap.toFun (f'.commutes c)) x
    simp only [map_add, DSmoothMap.add_apply, h, left_eq_add, map_sum, DSmoothMap.coe_sum,
      Finset.sum_apply, smul_eq_mul, map_mul, DSmoothMap.coe_mul, Pi.mul_apply]
    refine Finset.sum_eq_zero fun i _ ↦ mul_eq_zero_of_left ?_ _
    rw [map_sub, DSmoothMap.sub_apply, sub_eq_zero]
    exact (congrFun (congrArg (DSmoothMap.toFun ∘ f') (by ext; simp)) x).trans
      (b := f' (EuclideanSpace.proj i).toDSmoothMap x) (by simp [h, x'])
  preimage_map f := by
    refine DSmoothMap.ext fun x ↦ ?_
    simpa using (EuclideanSpace.basisFun _ ℝ).sum_repr (f x)

instance : CartSp.toCommAlgCatOp.Full := CartSp.toCommAlgCatOpFullyFaithful.full

instance : CartSp.toCommAlgCatOp.Faithful := CartSp.toCommAlgCatOpFullyFaithful.faithful

end Embeddings
