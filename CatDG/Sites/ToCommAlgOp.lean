import CatDG.Diffeology.Hadamard
import CatDG.Sites.CartSp
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Embeddings of sites into opposites of real algebras

This file constructs the functor `CartSp ⥤ (CommAlgCat ℝ)ᵒᵖ` sending each ℝⁿ to the algebra
of smooth real valued functions on it, and shows that this functor is fully faithful.

Eventually we'll want to do the same for `EuclOp` and `FinDimMfld`; for `EuclOp` this should
already be feasible, but for `FinDimMfld` we still lack a variant of Whitney's embedding theorem
for non-compact manifolds.

See https://ncatlab.org/nlab/show/embedding+of+smooth+manifolds+into+formal+duals+of+R-algebras.

## Main definitions / results:
* `CartSp.toCommAlgCatOp`: the fully faithful embedding of `CartSp` into `(CommAlgCat ℝ)ᵒᵖ`

## TODO
* Show that `EuclOp` embeds into `(CommAlgCat ℝ)ᵒᵖ` fully faithfully too
* Show that `FinDimMfld` embeds into `(CommAlgCat ℝ)ᵒᵖ` fully faithfully too
-/

universe u

open CategoryTheory

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
