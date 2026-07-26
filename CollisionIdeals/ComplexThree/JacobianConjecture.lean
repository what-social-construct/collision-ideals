import CollisionIdeals.ComplexThree.OffDiagonal
import CollisionIdeals.JacobianConjecture

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- Ax--Grothendieck specialized to complex affine three-space. -/
abbrev ComplexThreeAxGrothendieck : Prop :=
  ComplexAxGrothendieck 3

/-- The Jacobian conjecture in complex dimension three. -/
abbrev ComplexThreeJacobianConjecture : Prop :=
  ComplexJacobianConjecture 3

/-- A complex three-dimensional Keller map that is not an automorphism. -/
abbrev IsComplexThreeJacobianCounterexample
    (F : ComplexThreePolynomialMap) : Prop :=
  IsComplexJacobianCounterexample F

/--
Modulo Ax--Grothendieck, all possible dimension-three Jacobian
counterexamples are exactly the Keller maps with nonempty off-diagonal
collision scheme.
-/
theorem isComplexThreeJacobianCounterexample_iff_offDiagonal_nonempty
    (hAx : ComplexThreeAxGrothendieck)
    (F : ComplexThreePolynomialMap) :
    IsComplexThreeJacobianCounterexample F ↔
      IsComplexThreeKeller F ∧
        Nonempty (ComplexThreeOffDiagonalScheme F) := by
  change
    IsComplexJacobianCounterexample F ↔
      IsKeller F ∧ Nonempty (ComplexThreeOffDiagonalScheme F)
  rw [isComplexJacobianCounterexample_iff hAx F,
    complexThreeOffDiagonalScheme_nonempty_iff_obstructionIdeal_ne_bot]

end

end CollisionIdeals
