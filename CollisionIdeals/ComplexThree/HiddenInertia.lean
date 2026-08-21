import CollisionIdeals.ComplexThree.CubicS3
import CollisionIdeals.KellerCollisionModel

/-!
# Optional hidden-inertia consequence in complex dimension three

This file joins the cubic `S₃` result to the dimension-independent
normalization and inertia package.  Keeping this geometric corollary separate
lets the core cubic collision theorem compile without importing the Keller
collision-normalization model.
-/

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

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
