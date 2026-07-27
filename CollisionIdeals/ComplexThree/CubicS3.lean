import CollisionIdeals.ComplexThree.FunctionField
import CollisionIdeals.ComplexThree.JacobianConjecture
import CollisionIdeals.ComplexThree.OffDiagonal
import CollisionIdeals.ComplexThree.S3Collision
import CollisionIdeals.KellerCollisionModel

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

noncomputable section

open scoped TensorProduct

universe uN

/--
The structural dimension-three conclusion, without choosing coordinates
for a particular counterexample.

For a complex three-dimensional Keller map whose induced extension is
cubic and whose chosen normal-closure realization is the nonnormal
`S₃` case, the generic collision algebra is

`K ⊗_B C_F ≃ L × N`.

The first factor is the diagonal sheet.  The field `N` is the nonzero
off-diagonal ordered-root sheet, its `K`-automorphism group is `S₃`, and
the generic factor descends to a nonzero affine obstruction:

`obstructionIdeal F ≠ ⊥` and `collisionIdeal F < diagonalIdeal`.

The Keller hypothesis records the geometric setting.  The algebraic
factorization itself is supplied by the explicit generic, cubic,
normal-closure, and residual-field data below.
-/
theorem complexThreeCubicS3Collision
    (F : ComplexThreePolynomialMap)
    (hKeller : IsComplexThreeKeller F)
    (N : Type uN) [Field N]
    [Algebra ComplexThreeSourceFunctionField N]
    [Algebra (ComplexThreeBaseFunctionField F) N]
    [IsScalarTower
      (ComplexThreeBaseFunctionField F)
      ComplexThreeSourceFunctionField
      N]
    [Algebra.IsSeparable
      (ComplexThreeBaseFunctionField F)
      ComplexThreeSourceFunctionField]
    (normalClosure :
      NormalClosureData
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField
        N)
    (hmarked :
      normalClosure.embedding =
        IsScalarTower.toAlgHom
          (ComplexThreeBaseFunctionField F)
          ComplexThreeSourceFunctionField
          N)
    (hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F))
    (pb :
      PowerBasis
        (ComplexThreeBaseFunctionField F)
        ComplexThreeSourceFunctionField)
    (hdegree : pb.dim = 3)
    (residualEquiv :
      CubicResidualAlgebra
          (ComplexThreeBaseFunctionField F)
          ComplexThreeSourceFunctionField
          pb ≃ₐ[ComplexThreeSourceFunctionField] N)
    (hnontrivial :
      normalClosure.intermediateFixingSubgroup ≠ ⊥) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    IsComplexThreeJacobianCounterexample F ∧
      obstructionIdeal F ≠ ⊥ ∧
      collisionIdeal F <
        diagonalIdeal (R := ℂ) (ι := Fin 3) ∧
      Nonempty (ComplexThreeOffDiagonalScheme F) ∧
      Nonempty
        (((ComplexThreeBaseFunctionField F ⊗[
              polynomialMapImageAlgebra F] CollisionRing F) ≃ₐ[
                ComplexThreeBaseFunctionField F]
              ComplexThreeSourceFunctionField × N) ×
          CubicS3CollisionWitness
            (ComplexThreeBaseFunctionField F)
            ComplexThreeSourceFunctionField
            N pb) := by
  letI : Algebra
      (polynomialMapImageAlgebra F) (CollisionRing F) :=
    polynomialImageCollisionAlgebra F
  have hObstruction : obstructionIdeal F ≠ ⊥ :=
    polynomial_obstructionIdeal_ne_bot_of_cubicResidual
      F N hsurj pb residualEquiv
  have hStrict :
      collisionIdeal F <
        diagonalIdeal (R := ℂ) (ι := Fin 3) :=
    polynomial_collisionIdeal_lt_diagonalIdeal_of_cubicResidual
      F N hsurj pb residualEquiv
  have hOffDiagonal :
      Nonempty (ComplexThreeOffDiagonalScheme F) :=
    (complexThreeOffDiagonalScheme_nonempty_iff_obstructionIdeal_ne_bot
      F).2 hObstruction
  have hCounterexample :
      IsComplexThreeJacobianCounterexample F := by
    refine ⟨hKeller, ?_⟩
    intro hAutomorphism
    exact hObstruction
      (obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
        hAutomorphism)
  exact
    ⟨hCounterexample, hObstruction, hStrict, hOffDiagonal,
      exists_polynomialCubicS3CollisionWitness_of_normalClosure
        F N normalClosure hmarked hsurj pb hdegree residualEquiv
          hnontrivial⟩

/--
A ramified divisor in a cubic dimension-three Keller normalization model
realizes hidden inertia inside the same `S₃` normal closure.

The `S₃` statement concerns the full normal-closure Galois group.  The
divisor contributes a nontrivial inertia subgroup; core-freeness moves a
conjugate sheet, and the Keller étale bridge sends every such ramified
center into the deleted boundary.
-/
theorem complexThreeCubicS3HiddenInertiaAt
    (F : ComplexThreePolynomialMap)
    (M : PolynomialKellerCollisionModel F)
    (hdegree :
      Module.finrank
          (ComplexThreeBaseFunctionField F)
          ComplexThreeSourceFunctionField = 3)
    (hnontrivial :
      letI : Field M.N := M.fieldN
      letI : Algebra (ComplexThreeBaseFunctionField F) M.N :=
        M.algebraN
      M.diagram.cover.normalClosure.intermediateFixingSubgroup ≠ ⊥)
    (E :
      letI : Field M.N := M.fieldN
      letI : Algebra (ComplexThreeBaseFunctionField F) M.N :=
        M.algebraN
      PolynomialRamifiedCodimensionOnePoint
        (F := F) (N := M.N)) :
    letI : Field M.N := M.fieldN
    letI : Algebra (ComplexThreeBaseFunctionField F) M.N :=
      M.algebraN
    Nonempty
        ((M.N ≃ₐ[ComplexThreeBaseFunctionField F] M.N) ≃*
          Equiv.Perm (Fin 3)) ∧
      M.diagram.HasHiddenInertiaOrbit := by
  letI : Field M.N := M.fieldN
  letI : Algebra (ComplexThreeBaseFunctionField F) M.N :=
    M.algebraN
  refine ⟨⟨?s3⟩, ?hidden⟩
  · exact
      M.diagram.cover.normalClosure.galoisGroupEquivPermFinThree
        hdegree hnontrivial
  · exact
      M.hasHiddenInertiaOrbit_of_ramifiedCodimensionOnePoint E

end

end CollisionIdeals
