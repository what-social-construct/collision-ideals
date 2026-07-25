import CollisionIdeals.Basic
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace CollisionIdeals

/-- The coordinate ring of complex affine three-space. -/
abbrev ComplexThreePolynomial := SourceRing ℂ (Fin 3)

/-- A polynomial self-map of complex affine three-space. -/
abbrev ComplexThreePolynomialMap := Fin 3 → ComplexThreePolynomial

end CollisionIdeals
