# Categorical differential geometry in Lean

This project started out with the goal to formalise some of the basic theory of [orbifolds](https://en.wikipedia.org/wiki/Orbifold) in [Lean 4](https://lean-lang.org/), but over time evolved into a sort of general staging ground for formalisation of various kinds of generalised differential geometry. Currently, the repository consists mostly of material on [diffeological spaces](https://en.wikipedia.org/wiki/Diffeology) and [smooth spaces](https://ncatlab.org/nlab/show/smooth+set), but there are also formalisations of e.g. Frölicher spaces, cohesive topoi and various useful sites in the works. Current long-term goals include formalising the [Cahiers topos](https://ncatlab.org/nlab/show/Cahiers+topos) with its differential cohesion, the quasitopos of [concrete sheaves](https://ncatlab.org/nlab/show/concrete+sheaf) on any local site, and/or De-Rham cohomology of smooth spaces. Orbifolds will have to wait until there is enough material on higher category theory in mathlib to treat them properly; my hope is that the ongoing [infinity-cosmos project](https://github.com/emilyriehl/infinity-cosmos) will lay the groundwork for that.

## Overview

The material currently featured in this repository includes:
- Diffeology:
	- [basics & lattice structure on diffeologies](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Basic.html)
	- [induced and coinduced diffeologies, inductions and subductions](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Induced.html)
	- [basic constructions](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Constructions.html) (i.e. subspaces, quotient spaces, products, mapping spaces)
	- D-topology, [continuous diffeology](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Continuous.html)
	- [internal tangent spaces](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/TangentSpace.html)
	- [diffeological manifolds](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Manifolds.html) & [orbifolds](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/LocallyModelled.html)
	- [reflexive diffeological spaces](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Reflexive.html) (i.e. Frölicher spaces)
	- diffeological [monoids](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Algebra/Monoid.html), [groups](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Algebra/Group.html), rings and [modules / vector spaces](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Algebra/Module.html)
	- [pointwise algebraic structure of mapping spaces](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Algebra/DSmoothMap.html)
	- [category of diffeological spaces](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/DiffSp.html), limits & colimits in that category, cartesian-closedness and adjunctions to topological spaces & sets
- Smooth spaces:
	- sites [CartSp & EuclOp](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/Sites.html) as concrete subcanonical
	sites, the former being a cohesive, dense subsite of the latter
	- [category of smooth spaces](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Diffeology/SmoothSp.html), adjunction to diffeological spaces
- Cohesion:
	- [local sites](https://peabrainiac.github.io/lean-catdg/docs/CatDG/ForMathlib/LocalSite.html), [locally connected sites](https://peabrainiac.github.io/lean-catdg/docs/CatDG/ForMathlib/LocallyConnectedSite.html) and [cohesive sites](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Cohesive/CohesiveSite.html); also [concrete sites](https://peabrainiac.github.io/lean-catdg/docs/CatDG/ForMathlib/ConcreteSite.html)
	- [general cohesion](https://peabrainiac.github.io/lean-catdg/docs/CatDG/Cohesive/Basic.html)

Material that has been upstreamed from here to mathlib so far includes [delta-generated spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/DeltaGeneratedSpace.html), [global sections of sheaves](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/GlobalSections.html) and [adjoint triples](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Triple.html#CategoryTheory.Adjunction.Triple). More PRs are on the way / currently waiting for review.


## References

The formalisation of diffeology here is based mostly on Patrick Iglesias-Zemmour's excellent book "Diffeology" and mathlib's formalisation of topology, since there are a lot of parallels to topology in the basic theory. Other files are mostly derived from [the nlab](https://ncatlab.org/nlab/show/HomePage) and / various papers; I have made an effort to include proper attribution in the module docstring of each file.