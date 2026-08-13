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
  `PlanarKellerCollisionModel`, contains the normalization diagram, Keller
  bridges, and `ConjugateRamificationRealization`; from these data Lean
  canonically constructs the pulled-back conjugate boundary ideals and
  proves their valuation-theoretic containment at ramified divisors;
- `PlanarBoundaryCoherence` and `PlanarRamificationRigidity` are global and
  divisorial formulations of the same fixed-map endpoint.  Their universal
  validity is not proved; the formal interfaces use the explicit
  `BoundaryCoherenceBridge` and `RamificationRigidityBridge`, while
  moving-sheet coverage and boundary separation are alternative explicit
  codimension-one hypotheses;
- the manuscript proves the classical normal/Galois case by boundary-divisor
  rigidity and consequently excludes generic degree two; this argument is
  not yet part of the Lean development;
- branch purity is applied only after every height-one point has been shown
  unramified; finite-étale rigidity then gives $N=K$, and collision descent
  gives $q_F=0$ and $I_R=I_\Delta$;
- the stable boundary API canonically joins the inertia-fixed locus to the
  boundaries of all moved sheets.  Its fixed--moving local-cohomology
  specialization, together with the trace-dual, secant-to-trace, and
  logarithmic-inertia constructions, is retained as a prospective mechanism
  under the opt-in `CollisionIdeals.Planar.Research` umbrella; these are not
  steps in the stable divisorial endgame.  The underlying conjugate-secant
  evaluation and moved-sheet vanishing theorem itself is already proved;
- the manuscript proves the secant separability/trace-coevaluation identity
  and an explicit Hilbert--Burch presentation of a nonzero off-diagonal
  factor.  The remaining research theorem is a nonzero secant/frame
  multiplier landing the relevant principal parts in the finite trace-dual
  stage; these refinements are not yet formalized;
- the dimension-three theorem is an abstract implication from explicit
  cubic residual-field and marked-normal-closure data.  It concludes
  `IsComplexThreeJacobianCounterexample F`, but does not instantiate those
  conditions with a concrete polynomial map.
