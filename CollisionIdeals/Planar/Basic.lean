import CollisionIdeals.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

/-- The coordinate ring of the complex affine plane. -/
abbrev PlanePolynomial := SourceRing ℂ (Fin 2)

/-- The determinant of the `2 × 2` Jacobian matrix of a planar polynomial map. -/
def planarJacobianDet (F : Fin 2 → PlanePolynomial) : PlanePolynomial :=
  pderiv 0 (F 0) * pderiv 1 (F 1) -
    pderiv 1 (F 0) * pderiv 0 (F 1)

/-- A planar Keller map has a constant nonzero Jacobian determinant. -/
def IsPlanarKeller (F : Fin 2 → PlanePolynomial) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ planarJacobianDet F = C c

/--
The classical Ax--Grothendieck automorphism principle in the exact planar
form consumed by this project: an injective polynomial self-map of
`𝔸²_ℂ` is a polynomial automorphism.
-/
def PlanarAxGrothendieck : Prop :=
  ∀ F : Fin 2 → PlanePolynomial,
    Function.Injective (pointMap F) →
      IsPolynomialAutomorphism F

end

end CollisionIdeals
