import CollisionIdeals.Planar.ExternalAssumptions
import CollisionIdeals.Planar.GenericFiber

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/--
The internal hidden-inertia package for one planar map.

It supplies a finite normal-closure model, proves that every height-one
point of that model is unramified, and records the generic-fiber descent
from `L = K` to emptiness of the off-diagonal collision scheme.  Branch
purity and affine-plane finite-étale rigidity are deliberately not fields:
they enter only through the two explicit external interfaces.
-/
structure PlanarHiddenInertiaRigidity
    (F : Fin 2 → PlanePolynomial) where
  N : Type
  fieldN : Field N
  algebraN : Algebra (PlanarBaseFunctionField F) N
  cover :
    letI : Field N := fieldN
    letI : Algebra (PlanarBaseFunctionField F) N := algebraN
    PlanarNormalizedCover (F := F) (N := N)
  noCodimensionOneRamification :
    letI : Field N := fieldN
    letI : Algebra (PlanarBaseFunctionField F) N := algebraN
    NoCodimensionOneRamification (F := F) (N := N)
  genericDegreeOneExcludesOffDiagonal :
    PlanarFunctionFieldExtensionTrivial F →
      CollisionOffDiagonalVanishing F

namespace PlanarHiddenInertiaRigidity

variable {F : Fin 2 → PlanePolynomial}

/--
The two external algebraic-geometry inputs turn a hidden-inertia package
into the type-correct equality `L = K`.
-/
theorem functionFieldExtension_trivial
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (hHidden : PlanarHiddenInertiaRigidity F)
    (hKeller : IsPlanarKeller F) :
    PlanarFunctionFieldExtensionTrivial F := by
  letI : Field hHidden.N := hHidden.fieldN
  letI : Algebra (PlanarBaseFunctionField F) hHidden.N :=
    hHidden.algebraN
  have hEtale :
      AlgebraicGeometry.IsEtale
        (planarNormalizationInExtensionToBase
          (F := F) (N := hHidden.N)) :=
    hPurity hHidden.cover hKeller
      hHidden.noCodimensionOneRamification
  have hNormalClosure :
      hHidden.cover.normalClosure.ExtensionTrivial :=
    hFiniteEtaleRigidity hHidden.cover hKeller hEtale
  exact
    PlanarNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
      hHidden.cover.normalClosure hNormalClosure

end PlanarHiddenInertiaRigidity

/--
The conditional planar vanishing spine.

All normalization and hidden-inertia construction is carried by
`hHidden`; the only external algebraic-geometry inputs are branch purity
and finite-étale rigidity of the complex affine plane.
-/
theorem planarVanishing_of
    {F : Fin 2 → PlanePolynomial}
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (hHidden : PlanarHiddenInertiaRigidity F)
    (hKeller : IsPlanarKeller F) :
    obstructionIdeal F = ⊥ := by
  apply
    (collisionOffDiagonalVanishing_iff_obstructionIdeal_eq_bot F).mp
  exact
    hHidden.genericDegreeOneExcludesOffDiagonal
      (hHidden.functionFieldExtension_trivial
        hPurity hFiniteEtaleRigidity hKeller)

/--
The user-facing theorem with the two external algebraic-geometry
assumptions supplied by the dedicated assumptions module.
-/
theorem planarVanishing_assuming_externalAG
    {F : Fin 2 → PlanePolynomial}
    (hHidden : PlanarHiddenInertiaRigidity F)
    (hKeller : IsPlanarKeller F) :
    obstructionIdeal F = ⊥ :=
  planarVanishing_of
    ExternalAssumptions.branchPurityA2
    ExternalAssumptions.affinePlaneFiniteEtaleRigidity
    hHidden
    hKeller

end

end CollisionIdeals.Planar
