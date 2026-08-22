import CollisionIdeals.Planar.External.Interfaces
import CollisionIdeals.Planar.Statements.JacobianConjecture

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/-!
The three external literature inputs used by the planar divisorial endgame
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
