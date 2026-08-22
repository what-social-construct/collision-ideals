import CollisionIdeals.Planar.Basic
import CollisionIdeals.General.Normalization.Polynomial

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-!
# Planar normalization notation

The normalization, normal-closure, and Galois constructions are
dimension-independent and live in `PolynomialNormalization` and
`NormalClosure`.  This file contains only the conventional
`n = 2`, `k = ℂ` names actually used by the planar argument.
-/

/-- The image function field `K = ℂ(P,Q)`. -/
abbrev PlanarBaseFunctionField (F : PlanarPolynomialMap) :=
  PolynomialMapBaseFunctionField F

/-- The type-correct statement `K = L`. -/
abbrev PlanarFunctionFieldExtensionTrivial
    (F : PlanarPolynomialMap) : Prop :=
  PolynomialFunctionFieldExtensionTrivial F

section NormalExtension

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- The finite-model structure map `Z ⟶ Y`. -/
abbrev planarNormalizationInExtensionToBase :=
  polynomialNormalizationInExtensionToBase (F := F) (N := N)

/-- The finite normalized cover specialized to the complex affine plane. -/
abbrev PlanarNormalizedCover :=
  PolynomialNormalizedCover (F := F) (N := N)

end NormalExtension

end

end CollisionIdeals
