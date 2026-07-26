import CollisionIdeals.GenericFunctionField
import CollisionIdeals.Keller
import Mathlib.AlgebraicGeometry.Scheme

/-!
The affine morphism from polynomial source space to the spectrum of its
coordinate-image algebra.  This construction is independent of any Keller
or étaleness hypothesis.
-/

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]
variable {n : ℕ}

/-- The source affine space mapped to the spectrum of its coordinate image. -/
def polynomialSourceToImageBase
    (F : PolynomialSelfMap K n) :
    Spec (.of (SourceRing K (Fin n))) ⟶
      Spec (.of (polynomialMapImageAlgebra F)) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap
        (polynomialMapImageAlgebra F)
        (SourceRing K (Fin n))))

end

end CollisionIdeals
