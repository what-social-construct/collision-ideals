import CollisionIdeals.General.Automorphism.Statements
import CollisionIdeals.Planar.Basic

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- Ax--Grothendieck specialized to the complex affine plane. -/
abbrev PlanarAxGrothendieck : Prop :=
  ComplexAxGrothendieck 2

/--
The explicit complex-plane automorphism statement: every polynomial
self-map of `𝔸²_ℂ` with constant nonzero Jacobian determinant is a
polynomial automorphism of `𝔸²_ℂ`.
-/
abbrev PlanarJacobianConjecture : Prop :=
  ComplexJacobianConjecture 2

end

end CollisionIdeals
