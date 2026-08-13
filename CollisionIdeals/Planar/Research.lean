import CollisionIdeals.Planar.Research.PrincipalPartsStrategy
import CollisionIdeals.Planar.Research.FixedMovingBoundaryPrincipalParts
import CollisionIdeals.Planar.Research.FinitePrincipalPartsControl
import CollisionIdeals.Planar.ConjugateSecantEvaluation
import CollisionIdeals.Planar.Research.CompletedTameRamification

/-!
# Prospective planar rigidity mechanisms

This umbrella preserves the experimental modules behind the manuscript's
two-statements/one-morphism reduction without placing them in the stable
`CollisionIdeals.Planar` import spine:

* a hidden fixed--moving divisor produces an unbounded DVR pole tower;
* the trace dual supplies a finite bounded stage;
* the missing Keller-specific theorem is a nonzero secant/frame multiplier
  whose multiplication map factors through that stage.

The last item is not packaged as another abstract bridge here.  Constructing
it is the research problem, while the stable planar API begins only after the
height-one premise has been established.
-/
