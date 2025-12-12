import CatDG.Diffeology.DiffSp
import CatDG.Diffeology.Manifolds
import CatDG.ForMathlib.FinDimMfld

/-!
# Embeddings of categories of manifolds into the category of diffeological spaces

In this file we define the natural inclusion functors from categories of manifolds into the
category `DiffSp` of diffeological spaces, and show that some of them are fully faithful.

## Main definitions / results:
* Functors `Mfld ℝ ∞ ⥤ DiffSp` and `P.FullSubcategory ⥤ DiffSp` for any
  `P : ObjectProperty (Mfld ℝ ∞)`, both available as `forget₂`. Only the former is registered as a
  `HasForget₂` instance here, as a `HasForget₂` for restrictions to full subcategories is already
  available.
* `forget₂ : FinDimMfld ℝ ∞ ⥤ DiffSp` is fully faithful.

## TODO
* Show that `FinDimMfldWCorners ℝ ∞ ⥤ DiffSp` is fully faithful too, if it is. This is known to be
  true for manifolds with corners, but I haven't yet checked the details for manifolds with corners.
* Show that `BanachMfld ℝ ∞ ⥤ DiffSp` is fully faithful too. In the literature this is proven more
  generally for Frechet manifolds, but mathlib only has Banach manifolds for now. For the manifolds
  modelled on general normed spaces that mathlib has instead, this is presumably false because
  out of the many inequivalent notions of smoothness in normed spaces, mathlib has picked a
  different one than the one diffeological smoothness is equivalent to.
-/

universe u

open CategoryTheory ContDiff

/-- The category of (possibly non-Hausdorff, non-paracompact) smooth real manifolds with corners
carries a functor to the category of diffeological spaces that assigns to each manifold `M` the
diffeology `IsManifold.toDiffeology` given by all smooth maps from ℝⁿ to `M`. -/
noncomputable instance : HasForget₂ (Mfld ℝ ∞) DiffSp where
  forget₂ := {
    obj M := @DiffSp.of _ (IsManifold.toDiffeology M.modelWithCorners M)
    map {M N} f :=
      let := (IsManifold.toDiffeology M.modelWithCorners M)
      let := (IsManifold.toDiffeology N.modelWithCorners N)
      DiffSp.ofHom ⟨_, f.2.dsmooth⟩
  }

/-- In particular, every full subcategory of `Mfld ℝ ∞` has such a functor to `DiffSp` too. -/
noncomputable example {P : ObjectProperty (Mfld ℝ ∞)} : HasForget₂ P.FullSubcategory DiffSp :=
  inferInstance

namespace FinDimMfld

/-- For finite-dimensional manifolds, the inclusion into `DiffSp` is fully faithful. -/
def fullyFaithfulForgetToDiffSp : (forget₂ (FinDimMfld.{u, 0} ℝ ∞) DiffSp).FullyFaithful where
  preimage {M N} f := by
    change ContMDiffMap _ _ _ _ ∞
    exact ⟨f.hom, DSmooth.contMDiff (f.hom.dsmooth)⟩

instance : (forget₂ (FinDimMfld ℝ ∞) DiffSp).Full := fullyFaithfulForgetToDiffSp.full

/-- Faithfulness doesn't need to be registered as an instance because it is already available for
all forgetful functors `forget₂`. -/
example : (forget₂ (FinDimMfld ℝ ∞) DiffSp).Faithful := inferInstance

end FinDimMfld
