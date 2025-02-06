import Orbifolds.Diffeology.Induced

/-!
# Bundled smooth maps

Defines the type of smooth maps between diffeological spaces.
-/

universe u v

def DSmoothMap (X Y : Type*) [DiffeologicalSpace X] [DiffeologicalSpace Y] :=
  {f : X → Y // DSmooth f}

namespace DSmoothMap

variable {X Y Z : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y] [DiffeologicalSpace Z]

instance instFunLike : FunLike (DSmoothMap X Y) X Y where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

protected def toFun (f : DSmoothMap X Y) : X → Y := f.val

protected lemma dsmooth (f : DSmoothMap X Y) : DSmooth f := f.prop

@[simp]
lemma toFun_eq_coe {f : DSmoothMap X Y} : f.toFun = (f : X → Y) := rfl

theorem coe_injective ⦃f g : DSmoothMap X Y⦄ (h : (f : X → Y) = g) : f = g :=
  DFunLike.ext' h

@[ext]
lemma ext {f g : DSmoothMap X Y} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

nonrec def id : DSmoothMap X X := ⟨id,dsmooth_id⟩

def comp (f : DSmoothMap Y Z) (g : DSmoothMap X Y) : DSmoothMap X Z :=
  ⟨f ∘ g, (f.dsmooth).comp g.dsmooth⟩

def const (y : Y) : DSmoothMap X Y := ⟨fun _ ↦ y, dsmooth_const⟩

@[simp]
theorem coe_mk (f : X → Y) (h : DSmooth f) : @DFunLike.coe (DSmoothMap X Y) X _ _ ⟨f, h⟩ = f :=
  rfl

end DSmoothMap
