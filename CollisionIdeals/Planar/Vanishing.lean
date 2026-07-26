import CollisionIdeals.JacobianConjecture
import CollisionIdeals.Planar.Basic

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
The central planar vanishing statement:
the obstruction `I_Δ / I_R(F)` vanishes for every planar Keller map.

This definition records the theorem target without adding it as an axiom.
-/
abbrev PlanarVanishing : Prop :=
  ComplexKellerVanishing 2

/--
Planar vanishing is equivalent to equality of the collision and diagonal
ideals for every planar Keller map.
-/
theorem planarVanishing_iff_forall_collisionIdeal_eq_diagonalIdeal :
    PlanarVanishing ↔
      ∀ F : PlanarPolynomialMap,
        IsPlanarKeller F →
          collisionIdeal F = diagonalIdeal (R := ℂ) (ι := Fin 2) := by
  constructor
  · intro h F hF
    exact (obstructionIdeal_eq_bot_iff F).1 (h F hF)
  · intro h F hF
    exact (obstructionIdeal_eq_bot_iff F).2 (h F hF)

end

end CollisionIdeals
