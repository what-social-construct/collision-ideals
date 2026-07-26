import CollisionIdeals.Planar.Normalization
import CollisionIdeals.PolynomialNormalizationDiagram

/-!
# Planar normalization-diagram notation

The normalization diagram, its inertia indices, its conjugate centers, and
its hidden-orbit predicate are dimension-independent.  This file specializes
that API to `𝔸²_ℂ` and gives the generic no-hidden-orbit predicate its planar
theorem-target name.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- Absence of ramification at height-one points of the planar normal model. -/
abbrev NoCodimensionOneRamification : Prop :=
  PolynomialNoCodimensionOneRamification (F := F) (N := N)

/-- The normalization diagram specialized to a planar polynomial map. -/
abbrev NormalizationDiagram :=
  PolynomialNormalizationDiagram (F := F) (N := N)

/--
The specifically planar theorem target: a complete orbit of nontrivial
inertia cannot be hidden in the deleted affine-plane boundaries.

The underlying predicate is dimension-independent; only its proof is
expected to use planar geometry.
-/
abbrev PlanarNoHiddenInertia
    (D : NormalizationDiagram (F := F) (N := N)) : Prop :=
  PolynomialNormalizationDiagram.NoHiddenInertia D

end

end CollisionIdeals.Planar
