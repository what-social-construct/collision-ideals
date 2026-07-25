import CollisionIdeals.Planar.PurityRigidity
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Unramified.Locus

set_option autoImplicit false

namespace CollisionIdeals.Planar

open AlgebraicGeometry

noncomputable section

/--
The finite normal-closure model has no ramification at any height-one
prime.

This is the concrete local input consumed by branch purity.  It is stated
directly on every codimension-one point of the normalization ring, rather
than through an arbitrary family of valuation witnesses.
-/
def NoCodimensionOneRamification
    {F : Fin 2 → PlanePolynomial}
    {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N] : Prop :=
  letI : Algebra (planarImageAlgebra F) N :=
    planarNormalClosureBaseAlgebra (F := F) (N := N)
  ∀ q :
      PrimeSpectrum
        (PlanarNormalizationInExtensionRing (F := F) (N := N)),
    q.asIdeal.primeHeight = 1 →
      Algebra.IsUnramifiedAt
        (planarImageAlgebra F) q.asIdeal

/--
Specialized branch purity for a finite normal cover of the complex affine
plane.

The normalized-cover data already contains finiteness.  Under the planar
Keller hypothesis, unramifiedness at every height-one prime promotes to
étaleness of the entire normalization morphism.
-/
def BranchPurityA2 : Prop :=
  ∀ {F : Fin 2 → PlanePolynomial}
    {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N]
    (_M : PlanarNormalizedCover (F := F) (N := N)),
    IsPlanarKeller F →
      NoCodimensionOneRamification (F := F) (N := N) →
        IsEtale
          (planarNormalizationInExtensionToBase
            (F := F) (N := N))

/--
Triviality of connected finite étale covers of `𝔸²_ℂ`, specialized to the
normal-closure model.

The normalization is connected because its coordinate ring lies in the
field `N`, and finiteness is part of `PlanarNormalizedCover`.  The
type-correct conclusion `M.normalClosure.ExtensionTrivial` expresses
`N = K`.
-/
def AffinePlaneFiniteEtaleRigidity : Prop :=
  ∀ {F : Fin 2 → PlanePolynomial}
    {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N]
    (M : PlanarNormalizedCover (F := F) (N := N)),
    IsPlanarKeller F →
      IsEtale
          (planarNormalizationInExtensionToBase
            (F := F) (N := N)) →
        M.normalClosure.ExtensionTrivial

/-!
The two external algebraic-geometry inputs used by the conditional planar
spine.

They live in a dedicated namespace so every downstream dependency remains
visible in `#print axioms`.
-/
namespace ExternalAssumptions

/--
Mathematically standard branch-purity result, presently assumed because
the required theorem is not available in Mathlib.
-/
axiom branchPurityA2 : BranchPurityA2

/--
Mathematically standard triviality of connected finite étale covers of
`𝔸²_ℂ`, presently assumed because the required theorem is not available in
Mathlib.
-/
axiom affinePlaneFiniteEtaleRigidity :
  AffinePlaneFiniteEtaleRigidity

end ExternalAssumptions

end

end CollisionIdeals.Planar
