import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.CategoryTheory.Sites.Coverage
import Orbifolds.Cohesive.CohesiveSite
import Orbifolds.Diffeology.Algebra.DSmoothMap

/-!
# CartSp and EuclOp

This file defines the sites `CartSp` and `EuclOp` of cartesian spaces resp. open subsets of
cartesian spaces and smooth maps, both with the good open cover coverage. These
sites are of relevance because concrete sheaves on them correspond to diffeological spaces,
although sheaves on them are studied not in this file but in `Orbifolds.Diffeology.SmoothSp`.

See https://ncatlab.org/nlab/show/CartSp.

Note that with the current implementation, this could not be used to *define*
diffeological spaces - it already uses diffeology in the definition of
`CartSp.openCoverCoverage`. The reason is that smooth embeddings are apparently not yet
implemented in mathlib, so diffeological inductions are used instead.

Main definitions / results:
* `CartSp`: the category of euclidean spaces and smooth maps between them
* `CartSp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `CartSp` has all finite products
* `CartSp` is a cohesive site
* `EuclOp`: the category of open subsets of euclidean spaces and smooth maps between them
* `EuclOp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `CartSp.toEuclOp`: the fully faithful embedding of `CartSp` into `EuclOp`
* `CartSp.toEuclOp` exhibits `CartSp` as a dense sub-site of `EuclOp`

## TODO
* Switch from `HasForget` to the new `ConcreteCategory` design
* Generalise `CartSp` to take a smoothness parameter in `ℕ∞`
* Generalise `EuclOp` to take a smoothness parameter in `WithTop ℕ∞`
* General results about concrete sites
-/

universe u

open CategoryTheory Limits Sheaf TopologicalSpace

section CartSp

def CartSp := ℕ

instance : CoeSort CartSp Type where
  coe n := EuclideanSpace ℝ (Fin n)

instance (n : ℕ) : OfNat CartSp n where
  ofNat := n

instance : SmallCategory CartSp where
  Hom := fun n m ↦ DSmoothMap n m
  id := fun n ↦ DSmoothMap.id _
  comp := fun f g ↦ g.comp f

instance : HasForget CartSp where
  forget := { obj := fun n ↦ n, map := fun f ↦ f.1 }
  forget_faithful := { map_injective := fun {_ _} ↦ DSmoothMap.coe_injective }

instance CartSp.instFunLike (n m : CartSp) : FunLike (n ⟶ m) n m where
  coe f := DFunLike.coe (F := DSmoothMap _ _) f
  coe_injective' := DFunLike.coe_injective (F := DSmoothMap _ _)

@[simp]
theorem CartSp.id_app (n : CartSp) (x : n) : (𝟙 n : n ⟶ n) x = x := rfl

@[simp]
theorem CartSp.comp_app {n m k : CartSp} (f : n ⟶ m) (g : m ⟶ k) (x : n) :
    (f ≫ g : n → k) x = g (f x) := rfl

/-- The open cover coverage on `CartSp`, consisting of all coverings by open smooth embeddings.
  Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
  used instead. -/
def CartSp.openCoverCoverage : Coverage CartSp where
  covering n := {s | (∀ (m : _) (f : m ⟶ n), s f → Induction f.1 ∧ IsOpenMap f.1) ∧
    ⋃ (m : CartSp) (f ∈ s (Y := m)), Set.range f.1 = Set.univ}
  pullback n m g s hs := by
    use fun k ↦ {f | (∃ (k : _) (f' : k ⟶ n), s f' ∧ Set.range (g.1 ∘ f.1) ⊆ Set.range f'.1)
      ∧ Induction f.1 ∧ IsOpenMap f.1}
    refine ⟨⟨fun k f hf ↦ hf.2, ?_⟩, ?_⟩
    · refine Set.iUnion_eq_univ_iff.2 fun x ↦ ?_
      let ⟨k,hk⟩ := Set.iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := Set.mem_iUnion₂.1 hk
      refine ⟨m, Set.mem_iUnion₂.2 ?_⟩
      let ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1
        ((hs.1 k f hf).2.isOpen_range.preimage g.2.continuous) x hgx
      let e := (DDiffeomorph.univBall x hε)
      use ⟨_, dsmooth_subtype_val.comp e.dsmooth⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · refine ⟨k, f, hf, _root_.subset_trans ?_ (Set.image_subset_iff.2 hxε)⟩
        simp_rw [Set.range_comp]; apply Set.image_mono; simpa using subset_rfl
      · refine ⟨induction_subtype_val.comp e.induction, ?_⟩
        have := (Metric.isOpen_ball  (x := x) (ε := ε)).dTopCompatible
        exact (Metric.isOpen_ball).isOpenMap_subtype_val.comp e.toHomeomorph'.isOpenMap
      · change x ∈ Set.range (Subtype.val ∘ e.toEquiv)
        rw [e.toEquiv.surjective.range_comp]; simp [hε]
    · intro k f ⟨⟨k',f',hf'⟩,_⟩; use k'
      let f'' := (DDiffeomorph.ofInduction (hs.1 k' f' hf'.1).1)
      use ⟨_,(f''.dsmooth_invFun.comp <|
        (f ≫ g).2.subtype_mk (fun x ↦ hf'.2 (Set.mem_range_self x)))⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      simp_rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; exact congrArg Subtype.val <| f''.apply_symm_apply _

/-- The open cover grothendieck topology on `CartSp`. -/
def CartSp.openCoverTopology : GrothendieckTopology CartSp :=
  openCoverCoverage.toGrothendieck

/-- A sieve belongs to `CartSp.openCoverTopology` iff it contains a presieve from
`CartSp.openCoverCoverage`. -/
lemma CartSp.openCoverTopology.mem_sieves_iff {n : CartSp} {s : Sieve n} :
    s ∈ openCoverTopology n ↔ ∃ r, r ≤ s.arrows ∧ r ∈ openCoverCoverage n := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr⟩ ↦ Coverage.mem_toGrothendieck_sieves_of_superset _ hr.1 hr.2⟩
  induction h with
  | of n s hs =>
    exact ⟨s, Sieve.le_generate s, hs⟩
  | top n =>
    refine ⟨fun k f ↦ Induction f ∧ IsOpenMap f, le_top, fun k f hf ↦ hf, ?_⟩
    exact Set.univ_subset_iff.1 <| Set.subset_iUnion_of_subset n <|
        Set.subset_iUnion₂_of_subset (𝟙 n) ⟨induction_id, IsOpenMap.id⟩ (Set.range_id.symm.subset)
  | transitive n s r _ _ hs hr =>
    let ⟨s', hs'⟩ := hs
    refine ⟨fun k f ↦ r f ∧ Induction f ∧ IsOpenMap f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, ?_⟩
    rw [← Set.univ_subset_iff, ← hs'.2.2]
    refine Set.iUnion_subset fun m ↦ Set.iUnion₂_subset fun f hf ↦ ?_
    let ⟨r', hr'⟩ := hr (hs'.1 _ hf)
    simp_rw [← Set.image_univ, ← hr'.2.2, Set.image_iUnion]
    refine Set.iUnion_subset fun k ↦ Set.iUnion₂_subset fun g hg ↦ ?_
    refine Set.subset_iUnion_of_subset k <| Set.subset_iUnion₂_of_subset (g ≫ f) ⟨?_, ?_, ?_⟩ ?_
    · exact hr'.1 _ hg
    · exact (hs'.2.1 _ _ hf).1.comp (hr'.2.1 _ _ hg).1
    · exact (hs'.2.1 _ _ hf).2.comp (hr'.2.1 _ _ hg).2
    · rw [← Set.range_comp, Set.image_univ]; rfl

/- A sieve belongs to `CartSp.openCoverTopology` iff the open inductions in it are jointly
surjective. -/
lemma CartSp.openCoverTopology.mem_sieves_iff' {n : CartSp} {s : Sieve n} :
    s ∈ openCoverTopology n ↔
    ⋃ (m) (f : m ⟶ n) (_ : s f ∧ Induction f ∧ IsOpenMap f), Set.range f = Set.univ := by
  refine mem_sieves_iff.trans ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← Set.univ_subset_iff, ← hr.2.2]
    exact Set.iUnion_subset fun m ↦ Set.iUnion₂_subset fun f hf ↦ Set.subset_iUnion_of_subset m <|
      Set.subset_iUnion₂_of_subset f ⟨hr.1 _ hf, hr.2.1 m f hf⟩ subset_rfl
  · exact ⟨fun m f ↦ s f ∧ Induction f ∧ IsOpenMap f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, h⟩

/-- The `0`-dimensional cartesian space is terminal in `CartSp`. -/
def CartSp.isTerminal0 : IsTerminal (0 : CartSp) where
  lift s := DSmoothMap.const _ 0
  uniq c f h := by ext x; exact Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) (f x) 0

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (ι ⊕ κ)` and
`EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ`. Note that this is not an isometry because
product spaces are equipped with the supremum norm.
TODO: upstream -/
def EuclideanSpace.sumEquivProd {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] :
    EuclideanSpace 𝕜 (ι ⊕ κ) ≃L[𝕜] EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans <|
    WithLp.prodContinuousLinearEquiv _ _ _ _

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (Fin (n + m))` and
`EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)`.
TODO: upstream -/
def EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} :
    EuclideanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans
    sumEquivProd

/-- The first projection realising `EuclideanSpace ℝ (Fin (n + m))` as the product of
`EuclideanSpace ℝ n` and `EuclideanSpace ℝ m`. -/
noncomputable abbrev CartSp.prodFst {n m : CartSp} :
    @Quiver.Hom CartSp _ (@HAdd.hAdd ℕ ℕ _ _ n m) n :=
  DSmoothMap.fst.comp EuclideanSpace.finAddEquivProd.toDDiffeomorph.toDSmoothMap

/-- The second projection realising `EuclideanSpace ℝ (Fin (n + m))` as the product of
`EuclideanSpace ℝ n` and `EuclideanSpace ℝ m`. -/
noncomputable abbrev CartSp.prodSnd {n m : CartSp} :
    @Quiver.Hom CartSp _ (@HAdd.hAdd ℕ ℕ _ _ n m) m :=
  DSmoothMap.snd.comp EuclideanSpace.finAddEquivProd.toDDiffeomorph.toDSmoothMap

/-- The explicit binary fan of `EuclideanSpace ℝ n` and `EuclideanSpace ℝ m` given by
`EuclideanSpace ℝ (Fin (n + m))`. -/
noncomputable def CartSp.prodBinaryFan (n m : CartSp) : BinaryFan n m :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit. -/
noncomputable def CartSp.prodBinaryFanIsLimit (n m : CartSp) : IsLimit (prodBinaryFan n m) where
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
  refine @hasFiniteProducts_of_has_binary_and_terminal _ _ ?_ CartSp.isTerminal0.hasTerminal
  exact @hasBinaryProducts_of_hasLimit_pair _ _ ⟨⟨_, CartSp.prodBinaryFanIsLimit _ _⟩⟩

noncomputable instance : Unique (⊤_ CartSp) := by
  have : Unique ((forget CartSp).obj 0) := inferInstanceAs (Unique (Eucl 0))
  exact ((forget _).mapIso (terminalIsTerminal.uniqueUpToIso CartSp.isTerminal0)).toEquiv.unique

/-- `CartSp` is a locally connected site, roughly meaning that each of its objects is connected.
Note that this is different from `EuclOp`, which also contains disconnected open sets and thus isn't
locally connected. -/
instance : CartSp.openCoverTopology.IsLocallyConnectedSite where
  isConnected_of_mem {n} s hs := by
    simp_rw [CartSp.openCoverTopology.mem_sieves_iff', Set.eq_univ_iff_forall, Set.mem_iUnion] at hs
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
      refine ⟨Set.range f, hf.2.2.isOpen_range, ⟨y, hy⟩, fun x' ⟨y', hy'⟩ ↦ ?_⟩
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
instance : CartSp.openCoverTopology.IsCohesiveSite where
  nonempty_fromTerminal := ⟨DSmoothMap.const _ 0⟩

end CartSp

section EuclOp

def EuclOp := (n : ℕ) × Opens (EuclideanSpace ℝ (Fin n))

instance : CoeSort EuclOp Type where
  coe u := u.2

instance : SmallCategory EuclOp where
  Hom := fun u v ↦ DSmoothMap u v
  id := fun n ↦ DSmoothMap.id _
  comp := fun f g ↦ g.comp f

instance : HasForget EuclOp where
  forget := { obj := fun u ↦ u, map := fun f ↦ f.1 }
  forget_faithful := { map_injective := fun {_ _} ↦ DSmoothMap.coe_injective }

instance EuclOp.instFunLike (u v : EuclOp) : FunLike (u ⟶ v) u v where
  coe f := DFunLike.coe (F := DSmoothMap _ _) f
  coe_injective' := DFunLike.coe_injective (F := DSmoothMap _ _)

@[simp]
theorem EuclOp.id_app (u : EuclOp) (x : u) : (𝟙 u : u ⟶ u) x = x := rfl

@[simp]
theorem EuclOp.comp_app {u v w : EuclOp} (f : u ⟶ v) (g : v ⟶ w) (x : u) :
    (f ≫ g : u → w) x = g (f x) := rfl

/-- The open cover coverage on `EuclOp`, consisting of all coverings by open smooth embeddings.
  Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
  used instead. -/
def EuclOp.openCoverCoverage : Coverage EuclOp where
  covering u := {s | (∀ (v : _) (f : v ⟶ u), s f → Induction f.1 ∧ IsOpenMap f.1) ∧
    ⋃ (v : EuclOp) (f ∈ s (Y := v)), Set.range f.1 = Set.univ}
  pullback u v g s hs := by
    use fun k ↦ {f | (∃ (k : _) (f' : k ⟶ u), s f' ∧ Set.range (g.1 ∘ f.1) ⊆ Set.range f'.1)
      ∧ Induction f.1 ∧ IsOpenMap f.1}
    refine ⟨⟨fun k f hf ↦ hf.2, ?_⟩, ?_⟩
    · refine Set.iUnion_eq_univ_iff.2 fun x ↦ ?_
      let ⟨w,hw⟩ := Set.iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := Set.mem_iUnion₂.1 hw
      have h := v.2.2.isOpenMap_subtype_val _
        ((hs.1 _ _ hf).2.isOpen_range.preimage g.2.continuous')
      use ⟨_, _, h⟩
      refine Set.mem_iUnion₂.2 ⟨⟨_, dsmooth_inclusion (Subtype.coe_image_subset _ _)⟩, ?_⟩
      refine ⟨⟨⟨w, f, hf, ?_⟩, ?_, ?_⟩, ?_⟩
      · simp only [Opens.carrier_eq_coe, SetLike.coe_sort_coe]
        rw [Set.range_comp, Set.range_inclusion]
        convert Set.image_preimage_subset _ _; ext x
        rw [Set.mem_setOf_eq, Subtype.val_injective.mem_set_image]
      · exact induction_inclusion <| Subtype.coe_image_subset _ _
      · exact h.isOpenMap_inclusion <| Subtype.coe_image_subset _ _
      · dsimp; rw [Set.range_inclusion]; exact ⟨_, hgx, rfl⟩
    · intro k f ⟨⟨k',f',hf'⟩,_⟩; use k'
      let f'' := (DDiffeomorph.ofInduction (hs.1 k' f' hf'.1).1)
      use ⟨_,(f''.dsmooth_invFun.comp <|
        (f ≫ g).2.subtype_mk (fun x ↦ hf'.2 (Set.mem_range_self x)))⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      simp_rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; exact congrArg Subtype.val <| f''.apply_symm_apply _

/-- The open cover grothendieck topology on `EuclOp`. -/
def EuclOp.openCoverTopology : GrothendieckTopology EuclOp :=
  openCoverCoverage.toGrothendieck

/-- A sieve belongs to `EuclOp.openCoverTopology` iff it contains a presieve from
`EuclOp.openCoverCoverage`. -/
lemma EuclOp.openCoverTopology.mem_sieves_iff {n : EuclOp} {s : Sieve n} :
    s ∈ openCoverTopology n ↔ ∃ r, r ≤ s.arrows ∧ r ∈ openCoverCoverage n := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr⟩ ↦ Coverage.mem_toGrothendieck_sieves_of_superset _ hr.1 hr.2⟩
  induction h with
  | of n s hs =>
    exact ⟨s, Sieve.le_generate s, hs⟩
  | top n =>
    refine ⟨fun k f ↦ Induction f ∧ IsOpenMap f, le_top, fun k f hf ↦ hf, ?_⟩
    exact Set.univ_subset_iff.1 <| Set.subset_iUnion_of_subset n <|
        Set.subset_iUnion₂_of_subset (𝟙 n) ⟨induction_id, IsOpenMap.id⟩ (Set.range_id.symm.subset)
  | transitive n s r _ _ hs hr =>
    let ⟨s', hs'⟩ := hs
    refine ⟨fun k f ↦ r f ∧ Induction f ∧ IsOpenMap f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, ?_⟩
    rw [← Set.univ_subset_iff, ← hs'.2.2]
    refine Set.iUnion_subset fun m ↦ Set.iUnion₂_subset fun f hf ↦ ?_
    let ⟨r', hr'⟩ := hr (hs'.1 _ hf)
    simp_rw [← Set.image_univ, ← hr'.2.2, Set.image_iUnion]
    refine Set.iUnion_subset fun k ↦ Set.iUnion₂_subset fun g hg ↦ ?_
    refine Set.subset_iUnion_of_subset k <| Set.subset_iUnion₂_of_subset (g ≫ f) ⟨?_, ?_, ?_⟩ ?_
    · exact hr'.1 _ hg
    · exact (hs'.2.1 _ _ hf).1.comp (hr'.2.1 _ _ hg).1
    · exact (hs'.2.1 _ _ hf).2.comp (hr'.2.1 _ _ hg).2
    · rw [← Set.range_comp, Set.image_univ]; rfl

/- A sieve belongs to `EuclOp.openCoverTopology` iff the open inductions in it are jointly
surjective. -/
lemma EuclOp.openCoverTopology.mem_sieves_iff' {n : EuclOp} {s : Sieve n} :
    s ∈ openCoverTopology n ↔
    ⋃ (m) (f : m ⟶ n) (_ : s f ∧ Induction f ∧ IsOpenMap f), Set.range f = Set.univ := by
  refine mem_sieves_iff.trans ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← Set.univ_subset_iff, ← hr.2.2]
    exact Set.iUnion_subset fun m ↦ Set.iUnion₂_subset fun f hf ↦ Set.subset_iUnion_of_subset m <|
      Set.subset_iUnion₂_of_subset f ⟨hr.1 _ hf, hr.2.1 m f hf⟩ subset_rfl
  · exact ⟨fun m f ↦ s f ∧ Induction f ∧ IsOpenMap f, fun _ _ h ↦ h.1, fun _ _ h ↦ h.2, h⟩

/-- The embedding of `CartSp` into `EuclOp`. -/
noncomputable def CartSp.toEuclOp : CartSp ⥤ EuclOp where
  obj n := ⟨n, ⊤⟩
  map f := ⟨_, f.2.restrict (Set.mapsTo_univ f Set.univ)⟩

/-- Open subsets of cartesian spaces can be covered with cartesian spaces. -/
instance : CartSp.toEuclOp.IsCoverDense EuclOp.openCoverTopology := by
  constructor; intro u
  refine EuclOp.openCoverCoverage.mem_toGrothendieck_sieves_of_superset (R := ?_) ?_ ?_
  · exact fun {v} f ↦ v.2.1 = Set.univ ∧ Induction f.1 ∧ IsOpenMap f.1
  · intro v f hf
    refine ⟨⟨v.1, ⟨_, dsmooth_id.restrict (Set.mapsTo_univ _ _)⟩, ?_, ?_⟩⟩
    · let e : CartSp.toEuclOp.obj v.1 ⟶ v :=
        ⟨_, dsmooth_id.restrict (by convert Set.mapsTo_univ _ _; exact hf.1)⟩
      exact e ≫ f
    · ext x; rfl
  · refine ⟨fun v f hf ↦ hf.2, Set.iUnion_eq_univ_iff.2 fun x ↦ ?_⟩
    use ⟨u.1, ⊤⟩; apply Set.mem_iUnion₂.2
    let ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1 u.2.2 x.1 x.2
    let e := (DDiffeomorph.Set.univ _).trans (DDiffeomorph.univBall x.1 hε)
    use ⟨_, (dsmooth_inclusion hxε).comp e.dsmooth⟩
    refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
    · exact (induction_inclusion hxε).comp e.induction
    · have := (@isOpen_univ (EuclideanSpace ℝ (Fin u.1)) _).dTopCompatible
      have h : IsOpen (Metric.ball x.1 ε) := Metric.isOpen_ball
      have := h.dTopCompatible
      exact (h.isOpenMap_inclusion hxε).comp e.toHomeomorph'.isOpenMap
    · rw [Set.range_comp, e.surjective.range_eq, Set.image_univ]
      use ⟨x.1, Metric.mem_ball_self hε⟩; rfl

instance CartSp.toEuclOp_fullyFaithful : CartSp.toEuclOp.FullyFaithful where
  preimage {n m} f := by
    exact ⟨_, (dsmooth_subtype_val.comp f.2).comp (dsmooth_id.subtype_mk (Set.mem_univ))⟩

instance : CartSp.toEuclOp.Full := CartSp.toEuclOp_fullyFaithful.full

instance : CartSp.toEuclOp.Faithful := CartSp.toEuclOp_fullyFaithful.faithful

-- TODO: upstream to mathlib.
lemma IsOpenMap.restrict_mapsTo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsOpenMap f) {s : Set X} {t : Set Y} (hf' : Set.MapsTo f s t) (hs : IsOpen s) :
    IsOpenMap hf'.restrict :=
  (hf.restrict hs).codRestrict _

/-- `CartSp.toEuclOp` exhibits `CartSp` as a dense sub-site of `EuclOp` with respect to the
open cover topologies.
In particular, the sheaf topoi of the two sites are equivalent via `IsDenseSubsite.sheafEquiv`. -/
instance : CartSp.toEuclOp.IsDenseSubsite
    CartSp.openCoverTopology EuclOp.openCoverTopology where
  functorPushforward_mem_iff {n} s := by
    rw [CartSp.openCoverTopology.mem_sieves_iff', EuclOp.openCoverTopology.mem_sieves_iff']
    refine (DDiffeomorph.Set.univ (Eucl n)).injective.image_injective.eq_iff.symm.trans ?_
    rw [Set.image_univ, (DDiffeomorph.Set.univ (Eucl n)).surjective.range_eq]
    simp_rw [Set.image_iUnion, ← Set.range_comp]
    refine Eq.congr_left (subset_antisymm ?_ ?_)
    · refine Set.iUnion_subset fun u ↦ Set.iUnion₂_subset fun f hf ↦ ?_
      obtain ⟨m, g, h, hg, rfl⟩ := hf.1; replace hf := hf.2
      refine Set.range_subset_iff.2 fun x ↦ ?_
      let ⟨ε,hε,hε'⟩ := Metric.isOpen_iff.1 u.2.2 x.1 x.2
      let i : DSmoothMap _ _ := ⟨_, dsmooth_inclusion hε'⟩
      let e := DDiffeomorph.univBall x.1 hε
      refine Set.mem_iUnion_of_mem _ <| Set.mem_iUnion₂_of_mem
        (i := ⟨_, (DDiffeomorph.Set.univ _).dsmooth.comp <|
          h.dsmooth.comp <| i.dsmooth.comp e.dsmooth⟩ ≫ g) ⟨?_, ?_, ?_⟩ ?_
      · exact s.downward_closed hg _
      · exact (DDiffeomorph.Set.univ _).induction.comp <| hf.1.comp <|
          (induction_inclusion hε').comp e.induction
      · have : DTopCompatible (Metric.ball x.1 ε) := Metric.isOpen_ball.dTopCompatible
        have : DTopCompatible (Set.univ : Set (Eucl n)) := isOpen_univ.dTopCompatible
        exact (DDiffeomorph.Set.univ (Eucl n)).toHomeomorph'.isOpenMap.comp <| hf.2.comp <|
          (Metric.isOpen_ball.isOpenMap_inclusion hε').comp e.toHomeomorph'.isOpenMap
      use 0
      have h : i (e 0) = x := by ext1; simp_rw [← DDiffeomorph.coe_univBall_zero x.1 hε]; rfl
      simp_rw [← h]; rfl
    · refine Set.iUnion_subset fun m ↦ Set.iUnion₂_subset fun f hf ↦ ?_
      refine Set.subset_iUnion_of_subset _ <| Set.subset_iUnion₂_of_subset
        (CartSp.toEuclOp.map f) ⟨?_, ?_, ?_⟩ ?_
      · exact ⟨m, f, 𝟙 _, hf.1, (Category.id_comp _).symm⟩
      · exact hf.2.1.restrict (Set.mapsTo_univ _ _)
      · exact hf.2.2.restrict_mapsTo (Set.mapsTo_univ _ _) isOpen_univ
      · refine HasSubset.subset.trans_eq ?_
          (congrArg Set.range (Set.MapsTo.restrict_commutes _ _ _ (Set.mapsTo_univ _ _)).symm)
        rw [Set.range_comp, Subtype.range_val, ← Set.image_univ]; rfl

end EuclOp

/-!
### Embeddings into other categories
TODO: split this off into some other file, to reduce the imports of this file
-/

section Embeddings

example {n : ℕ} : DSmoothSMul ℝ (Eucl n) := inferInstance

/-- The embedding of `CartSp` into the opposite category of `ℝ`-algebras, sending each space `X`
to the algebra of smooth maps `X → ℝ`.
TODO: change this to the category of commutative algebras once #23601 is merged into mathlib -/
@[simps!]
noncomputable def CartSp.toAlgebraCatOp : CartSp ⥤ (AlgebraCat ℝ)ᵒᵖ where
  obj X := .op (.of ℝ (DSmoothMap X ℝ))
  map {n m} f := .op <| AlgebraCat.ofHom f.compRightAlgHom

noncomputable def CartSp.toAlgebraCatOpFullyFaithful : CartSp.toAlgebraCatOp.FullyFaithful where
  preimage {n m} f := by
    let f' (k : Fin m) : DSmoothMap _ _ := f.unop ⟨_, (EuclideanSpace.proj (𝕜 := ℝ) k).dsmooth⟩
    exact (∑ k, f' k • DSmoothMap.const (X := Eucl n) (EuclideanSpace.single k (1 : ℝ)):)
    /-exact ⟨_, dsmooth_finset_sum Finset.univ fun k _ ↦
      (f.unop ⟨_, (EuclideanSpace.proj k).dsmooth⟩).dsmooth.smul <|
        dsmooth_const (y := EuclideanSpace.single k (1 : ℝ))⟩-/
  map_preimage {n m} f := by
    refine Quiver.Hom.unop_inj ?_
    ext1; ext1 (g : DSmoothMap _ _)
    dsimp [DSmoothMap.compRightAlgHom, DSmoothMap.compRightRingHom]
    ext x
    --have := (ConcreteCategory.hom f.unop:)
    --have := DSmoothMap.compRightLinearMap' g (R := ℝ)
    -- TODO: finish this. might require something like Hadamard's lemma?
    sorry
  preimage_map f := by
    refine DSmoothMap.ext fun x ↦ ?_
    simpa using (EuclideanSpace.basisFun _ ℝ).sum_repr (f x)

instance : CartSp.toAlgebraCatOp.Full := CartSp.toAlgebraCatOpFullyFaithful.full

instance : CartSp.toAlgebraCatOp.Faithful := CartSp.toAlgebraCatOpFullyFaithful.faithful

end Embeddings
