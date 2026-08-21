import CollisionIdeals.Planar.Secant
import CollisionIdeals.UniversalProperty

/-!
# Evaluating the planar secant on collision sheets

This file follows the early planar secant relation through the universal
property of the collision ring.  For any pair of planar polynomial sheets
which agree after applying `F`, the evaluated secant determinant kills each
coordinate difference.  Over a domain, if the two sheets differ on a
coordinate, the secant determinant therefore evaluates to zero.

For conjugate generic sheets this is the precise formal endpoint of the
secant projector: it separates the diagonal sheet from a moving sheet.  Since
the secant evaluates to zero on the moving sheet, this result alone is not a
uniform annihilator by a nonzero boundary parameter; an additional comparison
with boundary principal parts is still required.
-/

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

universe u

/-- The class of the chosen planar secant determinant in the collision ring. -/
def planarSecantClass (F : PlanarPolynomialMap) : CollisionRing F :=
  Ideal.Quotient.mk (collisionIdeal F) (planarSecantDet F)

/--
In the collision ring, the planar secant class annihilates each coordinate
difference between the two universal sheets.
-/
theorem planarSecantClass_mul_coordinateDifference_eq_zero
    (F : PlanarPolynomialMap) (i : Fin 2) :
    planarSecantClass F *
        (collisionLeft F (X i) - collisionRight F (X i)) = 0 := by
  rw [planarSecantClass, collisionLeft_apply, collisionRight_apply,
    ← map_sub, ← map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply planarSecantDet_mul_diagonalIdeal_mem_collisionIdeal F
  simpa [diagonalGenerator] using
    (diagonalGenerator_mem (R := ℂ) i)

/--
After evaluating at any collision cocone, the secant determinant kills the
corresponding coordinate difference.
-/
theorem collisionLift_planarSecantClass_mul_coordinateDifference_eq_zero
    {T : Type u} [CommRing T] [Algebra ℂ T]
    (F : PlanarPolynomialMap) (c : CollisionCocone F T) (i : Fin 2) :
    collisionLift c (planarSecantClass F) *
        (c.left (X i) - c.right (X i)) = 0 := by
  have h := congrArg (collisionLift c)
    (planarSecantClass_mul_coordinateDifference_eq_zero F i)
  have hleft : collisionLift c (collisionLeft F (X i)) = c.left (X i) :=
    AlgHom.congr_fun (collisionLift_comp_left c) (X i)
  have hright : collisionLift c (collisionRight F (X i)) = c.right (X i) :=
    AlgHom.congr_fun (collisionLift_comp_right c) (X i)
  rw [← hleft, ← hright, ← map_sub, ← map_mul]
  exact h

/--
Over a domain, a collision cocone which moves one planar coordinate sends the
secant determinant to zero.
-/
theorem collisionLift_planarSecantClass_eq_zero_of_coordinate_moved
    {T : Type u} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (F : PlanarPolynomialMap) (c : CollisionCocone F T) (i : Fin 2)
    (hi : c.left (X i) ≠ c.right (X i)) :
    collisionLift c (planarSecantClass F) = 0 := by
  have h :=
    collisionLift_planarSecantClass_mul_coordinateDifference_eq_zero
      F c i
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hi)

/--
For a planar Keller map, a collision cocone which moves one coordinate kills
the concrete off-diagonal ideal.  This is the kernel statement needed to
factor its pair evaluation through `OffDiagonalRing F`.
-/
theorem collisionOffDiagonalIdeal_le_collisionPairMap_ker_of_coordinate_moved
    {T : Type u} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (c : CollisionCocone F T) (i : Fin 2)
    (hi : c.left (X i) ≠ c.right (X i)) :
    collisionOffDiagonalIdeal F ≤
      RingHom.ker (collisionPairMap c).toRingHom := by
  rw [collisionOffDiagonalIdeal_eq_planarSecantIdeal F hKeller,
    planarSecantIdeal, sup_le_iff]
  refine ⟨collisionIdeal_le_collisionPairMap_ker c, ?_⟩
  rw [Ideal.span_le]
  intro z hz
  simp only [Set.mem_singleton_iff] at hz
  subst z
  change collisionPairMap c (planarSecantDet F) = 0
  simpa [planarSecantClass, collisionLift] using
    collisionLift_planarSecantClass_eq_zero_of_coordinate_moved
      F c i hi

/--
The canonical evaluation of a moved planar collision sheet on the concrete
off-diagonal quotient.

Under the Keller and moved-coordinate hypotheses, this factorization is
supplied by the existing secant construction.  It is a generic/off-diagonal
map; it does not assert the boundary trace-landing statement for arbitrary
principal parts.
-/
def planarOffDiagonalLift
    {T : Type u} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (c : CollisionCocone F T) (i : Fin 2)
    (hi : c.left (X i) ≠ c.right (X i)) :
    OffDiagonalRing F →ₐ[ℂ] T :=
  Ideal.Quotient.liftₐ
    (collisionOffDiagonalIdeal F)
    (collisionPairMap c)
    (collisionOffDiagonalIdeal_le_collisionPairMap_ker_of_coordinate_moved
      F hKeller c i hi)

/-- The off-diagonal lift agrees with the original pair evaluation after
the quotient projection. -/
@[simp]
theorem planarOffDiagonalLift_comp_quotient
    {T : Type u} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (c : CollisionCocone F T) (i : Fin 2)
    (hi : c.left (X i) ≠ c.right (X i)) :
    (planarOffDiagonalLift F hKeller c i hi).comp
        (Ideal.Quotient.mkₐ ℂ (collisionOffDiagonalIdeal F)) =
      collisionPairMap c := by
  exact Ideal.Quotient.liftₐ_comp _ _ _

/-- The moved-sheet factorization is compatible with the canonical quotient
from the collision ring: it recovers the original collision lift. -/
@[simp]
theorem planarOffDiagonalLift_comp_collisionToOffDiagonal
    {T : Type u} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (c : CollisionCocone F T) (i : Fin 2)
    (hi : c.left (X i) ≠ c.right (X i)) :
    (planarOffDiagonalLift F hKeller c i hi).comp
        (collisionToOffDiagonal F) =
      collisionLift c := by
  apply Ideal.Quotient.algHom_ext
  rw [AlgHom.comp_assoc, collisionToOffDiagonal_comp_quotient,
    planarOffDiagonalLift_comp_quotient]
  exact (Ideal.Quotient.liftₐ_comp _ _ _).symm

/-- Elementwise form of `planarOffDiagonalLift_comp_quotient`. -/
@[simp]
theorem planarOffDiagonalLift_mk
    {T : Type u} [CommRing T] [IsDomain T] [Algebra ℂ T]
    (F : PlanarPolynomialMap) (hKeller : IsPlanarKeller F)
    (c : CollisionCocone F T) (i : Fin 2)
    (hi : c.left (X i) ≠ c.right (X i))
    (p : PairRing ℂ (Fin 2)) :
    planarOffDiagonalLift F hKeller c i hi
        (Ideal.Quotient.mk (collisionOffDiagonalIdeal F) p) =
      collisionPairMap c p := by
  rfl

end

end CollisionIdeals
