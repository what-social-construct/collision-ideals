import CollisionIdeals.General.Automorphism.Criteria
import CollisionIdeals.Planar.Rigidity.Consequences
import CollisionIdeals.Planar.Secant.Projector

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

namespace Planar

namespace PlanarKellerCollisionModel

variable {F : PlanarPolynomialMap}

/--
The planar divisorial endgame kills the chosen off-diagonal idempotent.

The concrete Keller collision model and the global no-hidden-inertia
hypothesis are displayed as separate inputs.
-/
theorem collisionIdempotent_eq_zero
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    planarCollisionIdempotent F M.keller = 0 := by
  apply
    (planarCollisionIdempotent_eq_zero_iff_ker_barMu_eq_bot
      F M.keller).2
  rw [collisionDiagonal_ker]
  exact
    planarVanishing_assuming_standardGeometry M hNoHidden

/--
The same divisorial endgame identifies the collision and diagonal ideals.
-/
theorem collisionIdeal_eq_diagonalIdeal
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    collisionIdeal F =
      diagonalIdeal (R := ℂ) (ι := Fin 2) := by
  exact
    (obstructionIdeal_eq_bot_iff F).1
      (planarVanishing_assuming_standardGeometry M hNoHidden)

/--
With Ax--Grothendieck supplied by the literature interface, the
planar divisorial endgame makes the Keller map a polynomial automorphism.
-/
theorem isPolynomialAutomorphism
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    IsPolynomialAutomorphism F :=
  planarAutomorphism_assuming_externalLiterature M hNoHidden

end PlanarKellerCollisionModel

end Planar

end

end CollisionIdeals
