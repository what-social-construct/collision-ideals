import CollisionIdeals.Planar.Basic
import CollisionIdeals.Planar.Statements.Vanishing

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

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
