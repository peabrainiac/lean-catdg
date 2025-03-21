import Orbifolds.ForMathlib.LocalSite
import Orbifolds.ForMathlib.LocallyConnectedSite

/-!
# Cohesive sites
Cohesive sites are sites with a number of useful properties that make their sheaf topos into
a cohesive topos. See https://ncatlab.org/nlab/show/cohesive+site.

Every cohesive site is in particular local and locally connected, and every cosifted category
with a terminal object that admits morphisms to every object is cohesive when equipped with
the trivial topology.
-/

universe u v w u₂ v₂

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A cohesive site is a cosifted locally connected site with a terminal object that admits
morphisms to every other object. This guarantees that the sheaf topos is a cohesive topos. -/
class GrothendieckTopology.IsCohesiveSite extends J.IsLocallyConnectedSite, IsSifted Cᵒᵖ,
    HasTerminal C where
  /-- For every object `X : C` there is at least one morphism from the terminal object to `X`. -/
  nonempty_fromTerminal {X} : Nonempty (⊤_ C ⟶ X)

/-- Every cohesive site is in particular a local site. -/
instance [J.IsCohesiveSite] : LocalSite J where
  eq_top_of_mem S hS := by
    rw [← S.id_mem_iff_eq_top]
    let ⟨f, hf⟩ := (IsLocallyConnectedSite.isConnected_of_mem S hS).is_nonempty
    let ⟨g⟩ := IsCohesiveSite.nonempty_fromTerminal (J := J) (X := f.left)
    exact terminal.hom_ext (𝟙 _) (g ≫ f.hom) ▸ S.downward_closed hf g

/-- Every cosifted category with a terminal object that admits morphisms to every other object
becomes a cohesive site when equipped with the trivial topology. -/
lemma isCohesiveSite_trivial {C : Type u} [Category.{v} C] [HasTerminal C] [IsSifted Cᵒᵖ]
    (h : ∀ X, Nonempty (⊤_ C ⟶ X)): (trivial C).IsCohesiveSite where
  nonempty_fromTerminal := h _
