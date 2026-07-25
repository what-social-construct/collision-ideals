import CollisionIdeals.Planar.Vanishing

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

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
