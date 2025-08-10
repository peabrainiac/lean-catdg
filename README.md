# Orbifolds in Lean

This project started out with the goal to formalise some of the basic theory of [orbifolds](https://en.wikipedia.org/wiki/Orbifold) in [Lean 4](https://lean-lang.org/), but over time evolved into a sort of general staging ground for formalisation of various kinds of generalised differential geometry. Currently, the repository consists mostly of material on [diffeological spaces](https://en.wikipedia.org/wiki/Diffeology) and [smooth spaces](https://ncatlab.org/nlab/show/smooth+set), but there are also formalisations of e.g. Frölicher spaces, cohesive topoi and various useful sites in the works. Current long-term goals include formalising the [Cahiers topos](https://ncatlab.org/nlab/show/Cahiers+topos) with its differential cohesion, the quasitopos of [concrete sheaves](https://ncatlab.org/nlab/show/concrete+sheaf) on any local site, and/or De-Rham cohomology of smooth spaces. Orbifolds will have to wait until there is enough material on higher category theory in mathlib to treat them properly; my hope is that the ongoing [infinity-cosmos project](https://github.com/emilyriehl/infinity-cosmos) will lay the groundwork for that.

## Overview

The material currently featured in this repository includes:
- Diffeology:
	- [basics & lattice structure on diffeologies](https://peabrainiac.github.io/lean-orbifolds/docs/Orbifolds/Diffeology/Basic.lean)
	- [induced and coinduced diffeologies, inductions and subductions](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Induced.lean)
	- [basic constructions](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Constructions.lean) (i.e. subspaces, quotient spaces, products, mapping spaces)
	- D-topology, [continuous diffeology](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Continuous.lean)
	- [internal tangent spaces](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/TangentSpace.lean)
	- [diffeological manifolds](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Manifolds.lean) & [orbifolds](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/LocallyModelled.lean)
	- [reflexive diffeological spaces](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Reflexive.lean) (i.e. Frölicher spaces)
	- diffeological [monoids](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Algebra/Monoid.lean), [groups](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Algebra/Group.lean), rings and [modules / vector spaces](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Algebra/Module.lean)
	- [pointwise algebraic structure of mapping spaces](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Algebra/DSmoothMap.lean)
	- [category of diffeological spaces](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/DiffSp.lean), limits & colimits in that category, cartesian-closedness and adjunctions to topological spaces & sets
- Smooth spaces:
	- sites [CartSp & EuclOp](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/Sites.lean) as concrete subcanonical
	sites, the former being a cohesive, dense subsite of the latter
	- [category of smooth spaces](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Diffeology/SmoothSp.lean), adjunction to diffeological spaces
- Cohesion:
	- [local sites](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/ForMathlib/LocalSite.lean), [locally connected sites](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/ForMathlib/LocallyConnectedSite.lean) and [cohesive sites](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Cohesive/CohesiveSite.lean); also [concrete sites](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/ForMathlib/ConcreteSite.lean)
	- [general cohesion](https://peabrainiac.github.io/lean-orbifolds/Orbifolds/Cohesive/Basic.lean)

Material that has been upstreamed from here to mathlib so far includes [delta-generated spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/DeltaGeneratedSpace.html), [global sections of sheaves](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/GlobalSections.html) and [adjoint triples](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Triple.html#CategoryTheory.Adjunction.Triple). More PRs are on the way / currently waiting for review.


## References

The formalisation of diffeology here is based mostly on Patrick Iglesias-Zemmour's excellent book "Diffeology" and mathlib's formalisation of topology, since there are a lot of parallels to topology in the basic theory. Other files are mostly derived from [the nlab](https://ncatlab.org/nlab/show/HomePage) and / various papers; I have made an effort to include proper attribution in the module docstring of each file.