# Orbifolds in Lean

This project started out with the goal to formalise some of the basic theory of [orbifolds](https://en.wikipedia.org/wiki/Orbifold) in [Lean 4](https://lean-lang.org/), but over time evolved into a sort of general staging ground for formalisation of various kinds of generalised differential geometry. Currently, the repository consists mostly of material on [diffeological spaces](https://en.wikipedia.org/wiki/Diffeology) and [smooth spaces](https://ncatlab.org/nlab/show/smooth+set), but there are also formalisations of e.g. Frölicher spaces, cohesive topoi and various useful sites in the works. Current long-term goals include formalising the [Cahiers topos](https://ncatlab.org/nlab/show/Cahiers+topos) with its differential cohesion, the quasitopos of [concrete sheaves](https://ncatlab.org/nlab/show/concrete+sheaf) on any local site, and/or De-Rham cohomology of smooth spaces. Orbifolds will have to wait until there is enough material on higher category theory in mathlib to treat them properly; my hope is that the ongoing [infinity-cosmos project](https://github.com/emilyriehl/infinity-cosmos) will lay the groundwork for that.

## Overview

The material currently featured in this repository includes:
- Diffeology:
	- [basics & lattice structure on diffeologies](./Orbifolds/Diffeology/Basic.lean)
	- [induced and coinduced diffeologies, inductions and subductions](./Orbifolds/Diffeology/Induced.lean)
	- [basic constructions](./Orbifolds/Diffeology/Constructions.lean) (i.e. subspaces, quotient spaces, products, mapping spaces)
	- D-topology, [continuous diffeology](./Orbifolds/Diffeology/Continuous.lean)
	- [internal tangent spaces](./Orbifolds/Diffeology/TangentSpace.lean)
	- [diffeological manifolds](./Orbifolds/Diffeology/Manifolds.lean) & [orbifolds](./Orbifolds/Diffeology/LocallyModelled.lean)
	- [reflexive diffeological spaces](./Orbifolds/Diffeology/Reflexive.lean) (i.e. Frölicher spaces)
	- diffeological [monoids](./Orbifolds/Diffeology/Algebra/Monoid.lean), [groups](./Orbifolds/Diffeology/Algebra/Group.lean), rings and [modules / vector spaces](./Orbifolds/Diffeology/Algebra/Module.lean)
	- [pointwise algebraic structure of mapping spaces](./Orbifolds/Diffeology/Algebra/DSmoothMap.lean)
	- [category of diffeological spaces](./Orbifolds/Diffeology/DiffSp.lean), limits & colimits in that category, cartesian-closedness and adjunctions to topological spaces & sets
- Smooth spaces:
	- sites [CartSp & EuclOp](./Orbifolds/Diffeology/Sites.lean)
	- [category of smooth spaces](./Orbifolds/Diffeology/SmoothSp.lean), adjunction to diffeological spaces
- Cohesion:
	- [local sites](./Orbifolds/ForMathlib/LocalSite.lean), [locally connected sites](./Orbifolds/ForMathlib/LocallyConnectedSite.lean) and [cohesive sites](./Orbifolds/Cohesive/CohesiveSite.lean)
	- [general cohesion](./Orbifolds/Cohesive/Basic.lean)

Other files that started out in this repository have also already made their way into mathlib, for example [delta-generated spaces](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/DeltaGeneratedSpace.html) and [global sections of sheaves](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/GlobalSections.html).


## References

The formalisation of diffeology here is based mostly on Patrick Iglesias-Zemmour's excellent book "Diffeology" and mathlib's formalisation of topology, since there are a lot of parallels to topology in the basic theory. Other files are mostly derived from [the nlab](https://ncatlab.org/nlab/show/HomePage) or various shorter papers; I have made an effort to include proper attribution in the module docstring of each file.