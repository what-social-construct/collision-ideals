import CollisionIdeals.AutomorphismCriterion
import CollisionIdeals.GenericDegreeOne
import CollisionIdeals.KellerCollisionModel
import CollisionIdeals.NormalClosure
import CollisionIdeals.Planar.ExternalAssumptions
import CollisionIdeals.Planar.NormalizationDiagram

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

/--
The shared Keller collision-normalization model, specialized to
`𝔸²_ℂ`.  Planar no-hidden-inertia remains a separate hypothesis.
-/
abbrev PlanarKellerCollisionModel
    (F : PlanarPolynomialMap) :=
  PolynomialKellerCollisionModel F

namespace PlanarKellerCollisionModel

variable {F : PlanarPolynomialMap}

/--
normal closure over the planar base field.  This is the type-correct
formal counterpart of `N = K`.
-/
theorem normalClosureExtensionTrivial
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    letI : Field M.N := M.fieldN
    letI : Algebra (PlanarBaseFunctionField F) M.N :=
      M.algebraN
    M.diagram.cover.normalClosure.ExtensionTrivial := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  have hNoCodimensionOneRamification :
      NoCodimensionOneRamification
        (F := F) (N := M.N) :=
    M.diagram.noCodimensionOneRamification
      M.ramifiedConjugateCentersInBoundary_of_keller
      hNoHidden
  have hNormalizationEtale :
      AlgebraicGeometry.IsEtale
        (planarNormalizationInExtensionToBase
          (F := F) (N := M.N)) :=
    hPurity M.diagram.cover hNoCodimensionOneRamification
  exact
    hFiniteEtaleRigidity M.diagram.cover hNormalizationEtale

/--
The two external algebraic-geometry inputs turn the Keller collision
model and the separate no-hidden-inertia hypothesis into the type-correct
equality `L = K`.
-/
theorem functionFieldExtensionTrivial
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    PlanarFunctionFieldExtensionTrivial F := by
  letI : Field M.N := M.fieldN
  letI : Algebra (PlanarBaseFunctionField F) M.N :=
    M.algebraN
  exact
    PolynomialNormalClosureData.functionFieldExtensionTrivial_of_extensionTrivial
      M.diagram.cover.normalClosure
      (M.normalClosureExtensionTrivial
        hPurity hFiniteEtaleRigidity hNoHidden)

end PlanarKellerCollisionModel

/--
The conditional planar vanishing spine.

All concrete normalization and collision data is carried by `M`.
The planar no-hidden-inertia statement and the two external
algebraic-geometry inputs remain explicit arguments.
-/
theorem planarVanishing_of
    {F : PlanarPolynomialMap}
    (hPurity : BranchPurityA2)
    (hFiniteEtaleRigidity : AffinePlaneFiniteEtaleRigidity)
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    obstructionIdeal F = ⊥ := by
  exact
    obstructionIdeal_eq_bot_of_functionFieldExtensionTrivial
      F (M.kellerFlat M.keller)
      (M.functionFieldExtensionTrivial
        hPurity hFiniteEtaleRigidity hNoHidden)

/--
The user-facing theorem with the two external algebraic-geometry
assumptions supplied by the dedicated assumptions module.
-/
theorem planarVanishing_assuming_standardGeometry
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    obstructionIdeal F = ⊥ :=
  planarVanishing_of
    ExternalAssumptions.branchPurityA2
    ExternalAssumptions.affinePlaneFiniteEtaleRigidity
    M hNoHidden

/--
Using the third external literature theorem, Ax--Grothendieck, the
conditional ideal-vanishing result yields a polynomial automorphism.
-/
theorem planarAutomorphism_assuming_externalLiterature
    {F : PlanarPolynomialMap}
    (M : PlanarKellerCollisionModel F)
    (hNoHidden :
      letI : Field M.N := M.fieldN
      letI : Algebra (PlanarBaseFunctionField F) M.N :=
        M.algebraN
      PlanarNoHiddenInertia M.diagram) :
    IsPolynomialAutomorphism F := by
  apply ExternalAssumptions.axGrothendieckA2 F
  exact
    pointMap_injective_of_collisionIdeal_eq_diagonalIdeal F
      ((obstructionIdeal_eq_bot_iff F).1
        (planarVanishing_assuming_standardGeometry M hNoHidden))

end

end CollisionIdeals.Planar
