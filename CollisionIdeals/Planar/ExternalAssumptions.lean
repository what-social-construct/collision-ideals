import CollisionIdeals.Planar.PurityRigidity
import CollisionIdeals.Planar.NormalizationDiagram

set_option autoImplicit false

namespace CollisionIdeals.Planar

open AlgebraicGeometry

noncomputable section

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
The three external literature inputs used by the conditional planar spine
and its final automorphism corollary.

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

/--
The classical Ax--Grothendieck theorem in the planar form used here,
presently assumed because the corresponding result is not available in
Mathlib.
-/
axiom axGrothendieckA2 : PlanarAxGrothendieck

end ExternalAssumptions

end

end CollisionIdeals.Planar
