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

/--
The minimal componentwise interface needed for the geometric planar proof.

An eventual scheme-theoretic instance should take `Component` to be the
connected components of the off-diagonal collision space,
`IsOffDiagonal` to mean nonempty and off-diagonal, and
`FirstProjectionFinite S` to mean that `p₁ : S → 𝔸²` is finite.
-/
structure PlanarCollisionComponentModel
    (F : Fin 2 → PlanePolynomial) where
  Component : Type
  IsOffDiagonal : Component → Prop
  FirstProjectionFinite : Component → Prop
  exists_offDiagonal_of_obstruction_ne_bot :
    obstructionIdeal F ≠ ⊥ →
      ∃ S, IsOffDiagonal S

/--
Finite-correspondence rigidity: a nonempty connected off-diagonal component
cannot be finite over the first projection.
-/
def FiniteCorrespondenceRigidity
    {F : Fin 2 → PlanePolynomial}
    (M : PlanarCollisionComponentModel F) : Prop :=
  ∀ S, M.IsOffDiagonal S → ¬ M.FirstProjectionFinite S

/--
The missing planar boundary statement: every nonempty connected
off-diagonal component would have to be finite over the first projection.
-/
def PlanarBoundaryFiniteness
    {F : Fin 2 → PlanePolynomial}
    (M : PlanarCollisionComponentModel F) : Prop :=
  ∀ S, M.IsOffDiagonal S → M.FirstProjectionFinite S

/--
For one planar map, componentwise finiteness and nonfiniteness force the
obstruction ideal to vanish.
-/
theorem obstructionIdeal_eq_bot_of_componentwise_finite_and_nonfinite
    {F : Fin 2 → PlanePolynomial}
    (M : PlanarCollisionComponentModel F)
    (hNonfinite : FiniteCorrespondenceRigidity M)
    (hFinite : PlanarBoundaryFiniteness M) :
    obstructionIdeal F = ⊥ := by
  by_contra hObstruction
  obtain ⟨S, hS⟩ :=
    M.exists_offDiagonal_of_obstruction_ne_bot hObstruction
  exact hNonfinite S hS (hFinite S hS)

/--
This is the complete logical architecture of the proposed planar proof.
Once the collision components are instantiated geometrically, finite-cover
rigidity and planar boundary finiteness imply `PlanarVanishing`.
-/
theorem planarVanishing_of_finite_and_nonfinite
    (model :
      ∀ F : Fin 2 → PlanePolynomial,
        PlanarCollisionComponentModel F)
    (hNonfinite :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          FiniteCorrespondenceRigidity (model F))
    (hFinite :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          PlanarBoundaryFiniteness (model F)) :
    PlanarVanishing := by
  intro F hF
  exact
    obstructionIdeal_eq_bot_of_componentwise_finite_and_nonfinite
      (model F) (hNonfinite F hF) (hFinite F hF)

end

end CollisionIdeals
