import CollisionIdeals.Planar.Basic

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
The central planar vanishing statement:
the obstruction `I_Δ / I_R(F)` vanishes for every planar Keller map.

This definition records the theorem target without adding it as an axiom.
-/
def PlanarVanishing : Prop :=
  ∀ F : Fin 2 → PlanePolynomial,
    IsPlanarKeller F →
      obstructionIdeal F = ⊥

/--
The kernel formulation of the planar theorem target: for every planar
Keller map, the canonical collision-to-diagonal quotient map is injective.

This definition records the statement without adding it as an axiom.
-/
def PlanarKernelVanishing : Prop :=
  ∀ F : Fin 2 → PlanePolynomial,
    IsPlanarKeller F →
      RingHom.ker (collisionDiagonalMap F) = ⊥

/--
The kernel formulation and obstruction-ideal formulation of planar
vanishing are identical.
-/
theorem planarKernelVanishing_iff_planarVanishing :
    PlanarKernelVanishing ↔ PlanarVanishing := by
  constructor
  · intro h F hKeller
    rw [← collisionDiagonalMap_ker F]
    exact h F hKeller
  · intro h F hKeller
    rw [collisionDiagonalMap_ker F]
    exact h F hKeller

/--
Planar vanishing is equivalent to equality of the collision and diagonal
ideals for every planar Keller map.
-/
theorem planarVanishing_iff_relationIdeals_equal :
    PlanarVanishing ↔
      ∀ F : Fin 2 → PlanePolynomial,
        IsPlanarKeller F →
          relationIdeal F = diagonalIdeal (R := ℂ) (ι := Fin 2) := by
  constructor
  · intro h F hF
    exact (obstructionIdeal_eq_bot_iff F).1 (h F hF)
  · intro h F hF
    exact (obstructionIdeal_eq_bot_iff F).2 (h F hF)

end

end CollisionIdeals
