import Mathlib.CategoryTheory.Sites.Coverage
--import Mathlib.CategoryTheory.Sites.Sheaf
import Orbifolds.Diffeology.DiffSp

/-!
# CartSp

This file defines `CartSp` as the category of cartesian spaces and smooth maps, equipped with
the open cover coverage. This makes it into a site, on which concrete sheaves correspond
directly to diffeological spaces.

See https://ncatlab.org/nlab/show/CartSp.

Note however that with the current implementation, this could not be used to *define*
diffeological spaces - it already uses diffeology in the definition of
`CartSp.openCoverCoverage`. The reason is that smooth embeddings are apparently not yet
implemented in mathlib, so diffeological inductions are used instead.

Main definitions / results:
* `CartSp`: the category of euclidean spaces and smooth maps between them
* `CartSp.openCoverCoverage`: the coverage given by jointly surjective open inductions
* `SmoothSp`: the category of smooth sets, as the category of sheaves on `CartSp`
* `DiffSp.toSmoothSp`: the embedding of diffeological spaces into smooth sets
-/

universe u

open CategoryTheory Sheaf

def CartSp := ℕ

instance : CoeSort CartSp Type where
  coe n := EuclideanSpace ℝ (Fin n)

instance (n : ℕ) : OfNat CartSp n where
  ofNat := n

instance : SmallCategory CartSp where
  Hom := fun n m => DSmoothMap n m
  id := fun n => DSmoothMap.id
  comp := fun f g => ⟨_,g.2.comp f.2⟩

instance : ConcreteCategory CartSp where
  forget := { obj := fun n => n, map := fun f => f.1 }
  forget_faithful := { map_injective := fun {_ _} => Subtype.coe_injective }

instance instFunLike (n m : CartSp) : FunLike (n ⟶ m) n m where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

@[simp]
theorem id_app (n : CartSp) (x : n) : (𝟙 n : n ⟶ n) x = x := rfl

@[simp]
theorem comp_app {n m k : CartSp} (f : n ⟶ m) (g : m ⟶ k) (x : n) :
    (f ≫ g : n → k) x = g (f x) := rfl

/-- The open cover coverage on `CartSp`, consisting of all coverings by open smooth embeddings.
  Since mathlib apparently doesn't have smooth embeddings yet, diffeological inductions are
  used instead. -/
def CartSp.openCoverCoverage : Coverage CartSp where
  covering n := {s | (∀ (m : _) (f : m ⟶ n), s f → Induction f.1 ∧ IsOpenMap f.1) ∧
    ⋃ (m : CartSp) (f ∈ s (Y := m)), Set.range f.1 = Set.univ}
  pullback n m g s hs := by
    use fun k => {f | (∃ (k : _) (f' : k ⟶ n), s f' ∧ Set.range (g.1 ∘ f.1) ⊆ Set.range f'.1)
      ∧ Induction f.1 ∧ IsOpenMap f.1}
    refine ⟨⟨fun k f hf => hf.2, ?_⟩, ?_⟩
    · refine Set.iUnion_eq_univ_iff.2 fun x => ?_
      let ⟨k,hk⟩ := Set.iUnion_eq_univ_iff.1 hs.2 (g x)
      let ⟨f,hf,hgx⟩ := Set.mem_iUnion₂.1 hk
      refine ⟨m, Set.mem_iUnion₂.2 ?_⟩
      let ⟨ε, hε, hxε⟩ := Metric.isOpen_iff.1
        ((hs.1 k f hf).2.isOpen_range.preimage g.2.continuous) x hgx
      let e := (DDiffeomorph.univBall x hε)
      use ⟨_, dsmooth_subtype_val.comp e.dsmooth⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · refine ⟨k, f, hf, subset_trans ?_ (Set.image_subset_iff.2 hxε)⟩
        simp_rw [Set.range_comp]; apply Set.image_mono; simp
      · refine ⟨induction_subtype_val.comp e.induction, ?_⟩
        have := (Metric.isOpen_ball  (x := x) (ε := ε)).dTopCompatible
        exact (Metric.isOpen_ball).isOpenMap_subtype_val.comp e.toHomeomorph'.isOpenMap
      · change x ∈ Set.range (Subtype.val ∘ e.toEquiv)
        rw [e.surjective.range_comp]; simp [hε]
    · intro k f ⟨⟨k',f',hf'⟩,_⟩; use k'
      let f'' := (DDiffeomorph.ofInduction (hs.1 k' f' hf'.1).1)
      use ⟨_,(f''.dsmooth_invFun.comp <|
        (f ≫ g).2.subtype_mk (fun x => hf'.2 (Set.mem_range_self x)))⟩
      refine ⟨f', hf'.1, ?_⟩; ext x; change f'.1 (f''.invFun _) = _
      simp_rw [show f'.1 = Subtype.val ∘ f'' by rfl]
      dsimp; rw [DDiffeomorph.apply_symm_apply,comp_apply]; rfl

/-- The open cover grothendieck topology on `CartSp`. -/
def CartSp.openCoverTopology : GrothendieckTopology CartSp :=
  openCoverCoverage.toGrothendieck

/-- The category of sheaves on `CartSp`, also known as *smooth spaces*. -/
def SmoothSp := SheafOfTypes CartSp.openCoverTopology

/-- This *should* be an instance already, but somehow could not be inferred.
  It doesn't make sense to me, but this seems to work for now. -/
instance : Category.{u,u+1} SmoothSp.{u} := SheafOfTypes.instCategory

/-- The embedding of diffeological spaces into smooth spaces. -/
def DiffSp.toSmoothSp : DiffSp.{u} ⥤ SmoothSp.{u} where
  obj X := ⟨{
    obj := fun n => DSmoothMap n.unop X
    map := fun f g => g.comp f.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl
  }, by
    rw [CartSp.openCoverTopology, Presieve.isSheaf_coverage]
    refine fun {n} s hs f hf => ?_
    have hs' : ∀ x : n, _ := fun x => Set.mem_iUnion.1 <| hs.2.symm ▸ Set.mem_univ x
    let k := fun x => (hs' x).choose
    have hk : ∀ x, ∃ f' : k x ⟶ n, _ := fun x => Set.mem_iUnion₂.1 (hs' x).choose_spec
    let f' := fun x => (hk x).choose
    have hf' : ∀ x, s (f' x) ∧ x ∈ Set.range (f' x).1 :=
      fun x => exists_prop.1 (hk x).choose_spec
    let f'' := fun x => f (f' x) (hf' x).1 (hf' x).2.choose
    have hf'' : ∀ l (g : l ⟶ n) (hg : s g), f'' ∘ g = f g hg := fun l g hg => by
      ext x
      dsimp [f'']
      have h := @hf _ _ 0 (DSmoothMap.const (hf' (g x)).2.choose)
        (DSmoothMap.const x) _ _ (hf' (g x)).1 hg
        (by ext; exact (hf' (g x)).2.choose_spec)
      exact DFunLike.congr_fun h 0
    refine ⟨⟨f'', ?_⟩, ?_, ?_⟩
    · refine dsmooth_iff_locally_dsmooth.2 fun x : n =>
        ⟨_, (hs.1 _ _ (hf' x).1).2.isOpen_range, (hf' x).2, ?_⟩
      rw [(DDiffeomorph.ofInduction (hs.1 _ _ (hf' x).1).1).subduction.dsmooth_iff]
      convert (f (f' x) (hf' x).1).2; exact hf'' (k x) (f' x) (hf' x).1
    · intro l g hg; ext x; exact congr_fun (hf'' l g hg) _
    · intro f''' hf'''; ext (x : n)
      rw [← (hf' x).2.choose_spec]
      exact (DFunLike.congr_fun (hf''' (f' x) (hf' x).1) _).trans
        (congr_fun (hf'' _ (f' x) (hf' x).1) _).symm⟩
  map f := ⟨{
    app := fun _ g => f.comp g
    naturality := fun _ _ _ => rfl
  }⟩
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
