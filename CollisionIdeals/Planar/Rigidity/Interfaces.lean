import CollisionIdeals.Planar.Rigidity.Statements

/-!
# Interfaces for the planar rigidity statements

These propositions isolate the geometric comparisons not yet formalized by
the development.  They are inputs to the proved rigidity consequences, not
axioms in this module.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/--
The geometric bridge for the global-boundary route.  It packages the
open-complement local-cohomology sequence and finite-open-immersion argument.
-/
def BoundaryCoherenceBridge : Prop :=
  ∀ (F : PlanarPolynomialMap),
    PlanarBoundaryCoherence F →
      polynomialIntermediateNormalizationBoundary F = ∅

/--
The bridge from finite-length Kähler differentials to the codimension-one
unramifiedness input consumed by purity.
-/
def RamificationRigidityBridge : Prop :=
  ∀ {F : PlanarPolynomialMap}
    {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N]
    (_M : PlanarNormalizedCover (F := F) (N := N)),
      PlanarRamificationRigidity (F := F) (N := N) →
        NoCodimensionOneRamification (F := F) (N := N)

end

end CollisionIdeals.Planar
