import CollisionIdeals.Planar.ExternalAssumptions
import CollisionIdeals.Planar.EtaleBoundary
import CollisionIdeals.Planar.GenericFiber
import CollisionIdeals.Planar.VisibleRamification

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/--
The internal hidden-inertia package for one planar map.

It supplies the normalization diagram and the standard valuation formula
realizing double-coset inertia indices as geometric ramification indices,
separately supplies the later planar boundary-rigidity theorem, and records
the generic-fiber descent from `L = K` to emptiness of the off-diagonal
collision scheme.

Branch purity and affine-plane finite-étale rigidity are deliberately not
fields: they enter only through the two explicit external interfaces.
-/
structure PlanarHiddenInertiaRigidity
    (F : Fin 2 → PlanePolynomial) where
  N : Type
  fieldN : Field N
  algebraN : Algebra (PlanarBaseFunctionField F) N
  diagram :
    letI : Field N := fieldN
    letI : Algebra (PlanarBaseFunctionField F) N := algebraN
    NormalizationDiagram (F := F) (N := N)
  kellerEtale : PlanarKellerEtaleBridge F
  ramificationRealization :
    letI : Field N := fieldN
    letI : Algebra (PlanarBaseFunctionField F) N := algebraN
    diagram.ConjugateRamificationRealization
  boundaryRigidity :
    letI : Field N := fieldN
    letI : Algebra (PlanarBaseFunctionField F) N := algebraN
    diagram.PlanarBoundaryRigidity
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
  have hNoCodimensionOneRamification :
      NoCodimensionOneRamification
        (F := F) (N := hHidden.N) :=
    hHidden.diagram.noCodimensionOneRamification
      (hHidden.diagram.visibleConjugateSheetInertia
        hHidden.ramificationRealization)
      hHidden.boundaryRigidity
      (hHidden.kellerEtale hKeller)
  have hNormalizationEtale :
      AlgebraicGeometry.IsEtale
        (planarNormalizationInExtensionToBase
          (F := F) (N := hHidden.N)) :=
    hPurity hHidden.diagram.cover hKeller
      hNoCodimensionOneRamification
  have hNormalClosure :
      hHidden.diagram.cover.normalClosure.ExtensionTrivial :=
    hFiniteEtaleRigidity hHidden.diagram.cover hKeller
      hNormalizationEtale
  exact
    PlanarNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
      hHidden.diagram.cover.normalClosure hNormalClosure

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

/--
Using the third external literature theorem, Ax--Grothendieck, the
conditional ideal-vanishing result yields a polynomial automorphism.
-/
theorem planarAutomorphism_assuming_externalLiterature
    {F : Fin 2 → PlanePolynomial}
    (hHidden : PlanarHiddenInertiaRigidity F)
    (hKeller : IsPlanarKeller F) :
    IsPolynomialAutomorphism F := by
  apply ExternalAssumptions.axGrothendieckA2 F
  exact
    pointMap_injective_of_relationIdeal_eq_diagonalIdeal F
      ((obstructionIdeal_eq_bot_iff F).1
        (planarVanishing_assuming_externalAG hHidden hKeller))

end

end CollisionIdeals.Planar
