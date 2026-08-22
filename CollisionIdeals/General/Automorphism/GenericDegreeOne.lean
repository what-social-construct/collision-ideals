import CollisionIdeals.General.GenericFiber.CollisionDiagonal
import Mathlib.RingTheory.Localization.BaseChange

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals

open scoped TensorProduct

noncomputable section

universe u v

open MvPolynomial

variable {R : Type u} [CommRing R] [IsDomain R]
variable {ι κ : Type v}

/--
If the induced function-field extension is trivial, the canonical map
`K ⊗_B A ⟶ L` is surjective.
-/
theorem polynomialGenericSourceTensorMap_surjective_of_extensionTrivial
    (F : κ → SourceRing R ι)
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    Function.Surjective (polynomialGenericSourceTensorMap F) := by
  intro z
  obtain ⟨k, hk⟩ := hTrivial z
  refine ⟨k ⊗ₜ (1 : SourceRing R ι), ?_⟩
  simpa [polynomialGenericSourceTensorMap] using hk

/--
After generic base change, the collision diagonal is injective when the
induced function-field extension has degree one.
-/
theorem polynomialGenericCollisionDiagonal_injective_of_extensionTrivial
    (F : κ → SourceRing R ι)
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    letI : Algebra
        (polynomialMapImageAlgebra F) (CollisionRing F) :=
      polynomialImageCollisionAlgebra F
    Function.Injective
      (Algebra.TensorProduct.map
        (AlgHom.id
          (PolynomialBaseFunctionField F)
          (PolynomialBaseFunctionField F))
        (polynomialImageCollisionDiagonal F)) := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  let K := PolynomialBaseFunctionField F
  let L := PolynomialSourceFunctionField (R := R) (ι := ι)
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  have hsurj :
      Function.Surjective (polynomialGenericSourceTensorMap F) :=
    polynomialGenericSourceTensorMap_surjective_of_extensionTrivial
      F hTrivial
  let φ : K ⊗[B] A ≃ₐ[K] L :=
    polynomialGenericSourceEquiv F hsurj
  have hmul :
      Function.Injective
        (diagonalMultiplication (B := K) (A := L)) :=
    diagonalMultiplication_injective_of_surjective hTrivial
  have hgeneric :
      Function.Injective
        (polynomialGenericCollisionDiagonal F hsurj) := by
    rw [← polynomialGenericCollisionEquiv_intertwines_diagonal F hsurj]
    exact hmul.comp (polynomialGenericCollisionEquiv F hsurj).injective
  have hcompat :
      polynomialGenericCollisionDiagonal F hsurj =
        φ.toAlgHom.comp
          (Algebra.TensorProduct.map
            (AlgHom.id K K)
            (polynomialImageCollisionDiagonal F)) := by
    rfl
  rw [hcompat] at hgeneric
  intro x y hxy
  apply hgeneric
  exact congrArg φ hxy

/--
Generic degree one kills the collision obstruction whenever the source
coordinate ring is flat over its coordinate image.
-/
theorem obstructionIdeal_eq_bot_of_functionFieldExtensionTrivial
    (F : κ → SourceRing R ι)
    (hFlat :
      Module.Flat
        (polynomialMapImageAlgebra F)
        (SourceRing R ι))
    (hTrivial : PolynomialFunctionFieldExtensionTrivial F) :
    obstructionIdeal F = ⊥ := by
  let B := polynomialMapImageAlgebra F
  let A := SourceRing R ι
  let C := CollisionRing F
  let K := PolynomialBaseFunctionField F
  letI : Algebra B C := polynomialImageCollisionAlgebra F
  letI : Module.Flat B A := hFlat
  letI : Module.Flat B C := polynomialCollisionRing_flat F
  have hDiagonal :
      Function.Injective (polynomialImageCollisionDiagonal F) :=
    injective_of_flat_source_of_baseChange
      (polynomialImageCollisionDiagonal F)
      (IsFractionRing.injective B K)
      (polynomialGenericCollisionDiagonal_injective_of_extensionTrivial
        F hTrivial)
  rw [← collisionDiagonal_ker]
  exact
    (RingHom.injective_iff_ker_eq_bot
      (polynomialImageCollisionDiagonal F).toRingHom).1 hDiagonal

end

end CollisionIdeals
