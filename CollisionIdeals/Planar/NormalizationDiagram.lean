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
The positive planar boundary obstruction: some nontrivial inertia orbit is
supported entirely in the deleted normalization boundary on every sheet on
which it has nontrivial relative index.
-/
abbrev PlanarHiddenInertia
    (D : NormalizationDiagram (F := F) (N := N)) : Prop :=
  PolynomialNormalizationDiagram.HasHiddenInertiaOrbit D

/--
Planar conjugate coverage: every ramified divisor has an inertia-moving
conjugate center which remains in the affine polynomial sheet.

This is the explicit center-theoretic form of the planar boundary question.
-/
def PlanarConjugateCoverage
    (D : NormalizationDiagram (F := F) (N := N)) : Prop :=
  ∀ E, ∃ q : D.sheetClasses E,
    1 < D.inertiaIndex E q ∧ D.ConjugateCenterVisible E q

/--
The planar boundary-exclusion premise: no complete orbit of nontrivial
inertia is hidden in the deleted affine-plane boundary.

This is deliberately a separate input, not a consequence of the
normalization package.
-/
abbrev PlanarNoHiddenInertia
    (D : NormalizationDiagram (F := F) (N := N)) : Prop :=
  PolynomialNormalizationDiagram.NoHiddenInertia D

/-- The negative and positive planar boundary predicates are exact negations. -/
theorem planarNoHiddenInertia_iff_not_planarHiddenInertia
    (D : NormalizationDiagram (F := F) (N := N)) :
    PlanarNoHiddenInertia D ↔ ¬ PlanarHiddenInertia D :=
  Iff.rfl

/-- An inertia-moving affine conjugate center rules out a hidden orbit. -/
theorem noHiddenInertia_of_conjugateCoverage
    (D : NormalizationDiagram (F := F) (N := N))
    (hCoverage : PlanarConjugateCoverage D) :
    PlanarNoHiddenInertia D := by
  intro hHidden
  obtain ⟨E, _, hBoundary⟩ := hHidden
  obtain ⟨q, hq, hVisible⟩ := hCoverage E
  exact (hBoundary q (Nat.ne_of_gt hq)) hVisible

end

end CollisionIdeals.Planar
