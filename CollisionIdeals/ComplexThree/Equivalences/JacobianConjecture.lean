import CollisionIdeals.ComplexThree.OffDiagonal
import CollisionIdeals.ComplexThree.Statements.JacobianConjecture
import CollisionIdeals.General.Automorphism.Equivalences

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

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
