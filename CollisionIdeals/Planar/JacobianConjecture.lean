import CollisionIdeals.JacobianConjecture
import CollisionIdeals.Planar.Basic
import CollisionIdeals.Planar.Vanishing

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

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

/--
Assuming the classical Ax--Grothendieck principle, the obstruction detects
polynomial automorphisms map by map.
-/
theorem planarPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
    (hAx : PlanarAxGrothendieck)
    (F : PlanarPolynomialMap) :
    IsPolynomialAutomorphism F ↔
      obstructionIdeal F = ⊥ :=
  complexPolynomialAutomorphism_iff_obstructionIdeal_eq_bot hAx F

/--
Modulo Ax--Grothendieck, a polynomial self-map of the complex affine plane
is a polynomial automorphism exactly when its collision-to-diagonal map is
injective.
-/
theorem planarPolynomialAutomorphism_iff_collisionDiagonal_injective
    (hAx : PlanarAxGrothendieck)
    (F : PlanarPolynomialMap) :
    IsPolynomialAutomorphism F ↔
      Function.Injective (collisionDiagonal F) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  change
    IsPolynomialAutomorphism F ↔
      RingHom.ker (collisionDiagonal F).toRingHom = ⊥
  rw [collisionDiagonal_ker]
  exact
    planarPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
      hAx F

/--
Modulo the classical Ax--Grothendieck theorem, the usual planar Jacobian
conjecture is exactly vanishing of `I_Δ / I_R` for every planar Keller map.
-/
theorem planarJacobianConjecture_iff_planarVanishing
    (hAx : PlanarAxGrothendieck) :
    PlanarJacobianConjecture ↔ PlanarVanishing :=
  complexJacobianConjecture_iff_kellerVanishing hAx

end

end CollisionIdeals
