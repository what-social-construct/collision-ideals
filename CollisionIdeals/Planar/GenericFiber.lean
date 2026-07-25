import CollisionIdeals.OffDiagonalScheme
import CollisionIdeals.Planar.Normalization

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/--
The generic-fiber bridge used after normalization:

if a planar Keller map has trivial function-field extension
`ℂ(P,Q) ⊂ ℂ(x,y)`, then its off-diagonal collision scheme is empty.

Geometrically, a nonempty component of the étale self-fiber product has
open image under the first projection and therefore contributes another
generic sheet.  This definition isolates that standard geometric lemma;
it does not add it as an axiom.
-/
def PlanarGenericDegreeOneExcludesOffDiagonal : Prop :=
  ∀ (F : Fin 2 → PlanePolynomial),
    IsPlanarKeller F →
      PlanarFunctionFieldExtensionTrivial F →
        CollisionOffDiagonalVanishing F

/--
The generic-degree-one bridge kills the obstruction ideal for one planar
Keller map.
-/
theorem obstructionIdeal_eq_bot_of_planarFunctionField_trivial
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal)
    (F : Fin 2 → PlanePolynomial)
    (hKeller : IsPlanarKeller F)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    obstructionIdeal F = ⊥ :=
  (collisionOffDiagonalVanishing_iff_obstructionIdeal_eq_bot F).mp
    (hGeneric F hKeller hTrivial)

/--
Equivalently, the canonical collision-to-diagonal map has zero kernel.
-/
theorem collisionDiagonalMap_ker_eq_bot_of_planarFunctionField_trivial
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal)
    (F : Fin 2 → PlanePolynomial)
    (hKeller : IsPlanarKeller F)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    RingHom.ker (collisionDiagonalMap F) = ⊥ := by
  rw [collisionDiagonalMap_ker]
  exact
    obstructionIdeal_eq_bot_of_planarFunctionField_trivial
      hGeneric F hKeller hTrivial

/--
Equivalently, the collision and diagonal ideals agree.
-/
theorem relationIdeal_eq_diagonalIdeal_of_planarFunctionField_trivial
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal)
    (F : Fin 2 → PlanePolynomial)
    (hKeller : IsPlanarKeller F)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    relationIdeal F =
      diagonalIdeal (R := ℂ) (ι := Fin 2) :=
  (obstructionIdeal_eq_bot_iff F).mp
    (obstructionIdeal_eq_bot_of_planarFunctionField_trivial
      hGeneric F hKeller hTrivial)

/--
The exact end-to-end planar reduction.

Once finite-completion/open-immersion inputs, normalization rigidity, and
the generic-fiber collision lemma are supplied, planar obstruction
vanishing follows formally.
-/
theorem planarVanishing_of_normalizationRigidity
    (hFinite :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          IsPlanarFiniteCompletion F)
    (hOpen :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          IsPlanarIntermediateOpen F)
    (hRigidity : PlanarNormalizationRigidity)
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal) :
    PlanarVanishing := by
  intro F hKeller
  exact
    obstructionIdeal_eq_bot_of_planarFunctionField_trivial
      hGeneric F hKeller
        (hRigidity F hKeller
          (hFinite F hKeller)
          (hOpen F hKeller))

end

end CollisionIdeals
