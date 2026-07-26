# Paper

Build the paper from this directory with:

```bash
latexmk -pdf main.tex
```

The paper follows the Lean dependency spine.  Every mathematical section
ends with the corresponding Lean source files.

The status distinction in the paper is intentional:

- branch purity, finite-étale rigidity of `𝔸²_ℂ`, and
  Ax–Grothendieck are standard literature theorems represented by explicit
  interfaces in Lean;
- a supplied `PolynomialKellerCollisionModel`, specialized as
  `PlanarKellerCollisionModel`, contains the normalization diagram,
  Keller bridges, and `ConjugateRamificationRealization`; constructing
  that model and proving Planar No-Hidden-Inertia remain separate planar
  inputs;
- the planar conclusion proved in Lean is first local unramifiedness at
  every height-one point, not a separately formalized equality of all
  inertia groups;
- the dimension-three theorem is an abstract implication from explicit
  cubic residual-field and marked-normal-closure data.  It concludes
  `IsComplexThreeJacobianCounterexample F`, but does not instantiate those
  conditions with a concrete polynomial map.
