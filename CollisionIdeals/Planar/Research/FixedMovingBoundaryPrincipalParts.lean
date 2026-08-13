import CollisionIdeals.BoundaryPrincipalParts
import CollisionIdeals.Planar.BoundarySeparation

/-!
# Fixed--moving boundary principal parts

The stable boundary API supplies the canonical ideal
`fixedMovingBoundaryIdeal D C`.  This research module applies the general
`BoundaryPrincipalParts` construction directly to that ideal.  Height one is
deliberately absent from these definitions: it enters only when the module is
localized at a divisorial point and passed to the purity endgame.

No successive-support spectral sequence, DVR localization, equivariant
character calculation, or secant--trace landing theorem is asserted here.
-/

set_option autoImplicit false

open CategoryTheory

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- First local cohomology supported on the canonical fixed--moving locus. -/
def FixedMovingBoundaryPrincipalParts
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) :
    ModuleCat (GaloisNormalizationRing (F := F) (N := N)) :=
  BoundaryPrincipalParts
    (GaloisNormalizationRing (F := F) (N := N))
    (fixedMovingBoundaryIdeal D C)

/-- The abstract uniform-annihilator target for the fixed--moving module. -/
def HasUniformFixedMovingBoundaryAnnihilator
    (D : NormalizationDiagram (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D)) : Prop :=
  HasUniformIdealPowerAnnihilator
    (GaloisNormalizationRing (F := F) (N := N))
    (fixedMovingBoundaryIdeal D C)
    (FixedMovingBoundaryPrincipalParts D C)

end

end CollisionIdeals.Planar
