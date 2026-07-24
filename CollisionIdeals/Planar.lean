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
The central planar vanishing statement:
the collision ideal of every planar Keller map is the diagonal ideal.

This definition records the theorem target without adding it as an axiom.
-/
def PlanarVanishing : Prop :=
  ∀ F : Fin 2 → PlanePolynomial,
    IsPlanarKeller F →
      relationIdeal F = diagonalIdeal (R := ℂ) (ι := Fin 2)

/--
Planar vanishing is exactly vanishing of the obstruction ideal for every
planar Keller map.
-/
theorem planarVanishing_iff_obstruction_vanishes :
    PlanarVanishing ↔
      ∀ F : Fin 2 → PlanePolynomial,
        IsPlanarKeller F → obstructionIdeal F = ⊥ := by
  constructor
  · intro h F hF
    exact (obstructionIdeal_eq_bot_iff F).2 (h F hF)
  · intro h F hF
    exact (obstructionIdeal_eq_bot_iff F).1 (h F hF)

end

end CollisionIdeals
