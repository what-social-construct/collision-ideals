import CollisionIdeals.Planar.Research.PrincipalPartsStrategy
import CollisionIdeals.Planar.Research.FixedMovingBoundaryPrincipalParts
import CollisionIdeals.Planar.Research.FinitePrincipalPartsControl
import CollisionIdeals.Planar.ConjugateSecantEvaluation
import CollisionIdeals.Planar.ExplicitSecant
import CollisionIdeals.Planar.KellerFrame
import CollisionIdeals.Planar.Research.SecantFrameDenominator
import CollisionIdeals.Planar.Research.MonogenicOrder
import CollisionIdeals.Planar.Research.CompletedTameRamification

/-!
# Prospective planar rigidity mechanisms

This umbrella preserves the experimental modules behind the manuscript's
two-statements/one-morphism reduction without placing them in the stable
`CollisionIdeals.Planar` import spine:

* a hidden fixed--moving divisor produces an unbounded DVR pole tower;
* the trace dual supplies a finite bounded stage;
* explicit divided differences and the polynomial Keller frame supply a
  canonical finite coefficient package with a nonzero denominator ideal;
* a chosen integral primitive generator for the secant--trace comparison uses
  Mathlib's monogenic order, power basis, hypersurface presentation, Jacobian
  element, and conductor directly;
* the missing Keller-specific theorem says that this prescribed ideal is
  contained in the trace transporter for the whole pole tower.

The last item is not packaged as another abstract bridge here.  Constructing
it is the research problem, while the stable planar API begins only after the
height-one premise has been established.
-/
