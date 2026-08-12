import CollisionIdeals.Planar.PrincipalPartsStrategy
import CollisionIdeals.Planar.UnboundedPrincipalParts
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite control of planar principal parts

This file formalizes an abstract exclusion criterion.  A comparison injection
from the ramification-supported principal-parts module into any finite module
makes the former finite over a Noetherian ring.

For the intended geometric application, the trace dual naturally embeds as a
bounded-pole submodule of principal parts, not conversely.  Thus the structure
below is not claimed to arise formally from finite flatness: constructing it
would already exclude hidden unbounded principal parts.  The more intrinsic
target is a Keller/secant-derived uniform different-power annihilator, or an
equivalent theorem forcing all relevant classes into one bounded codifferent
stage.

Combining such finite control with the unbounded-pole conclusion of
`UnboundedPrincipalParts` gives the contradiction immediately.  Constructing
the comparison from the planar Keller geometry remains the substantive
missing theorem.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

universe u v w

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (Q : Type w) [AddCommGroup Q] [Module R Q]

/--
Finite coherent control of a principal-parts module by an injective
comparison with a finite target.
-/
structure FinitePrincipalPartsControl where
  target_finite : Module.Finite R Q
  comparison : M →ₗ[R] Q
  comparison_injective : Function.Injective comparison

namespace FinitePrincipalPartsControl

variable {R M Q}

/-- Finite coherent control makes the principal-parts module finite. -/
theorem source_finite
    [IsNoetherianRing R]
    (C : FinitePrincipalPartsControl R M Q) :
    Module.Finite R M := by
  letI : Module.Finite R Q := C.target_finite
  exact Module.Finite.of_injective C.comparison C.comparison_injective

/--
The two proposed paths meet in an immediate contradiction: a module cannot
simultaneously have finite coherent control and unbounded locally
power-torsion principal parts.
-/
theorem contradiction_of_unboundedPowerTorsion
    [IsNoetherianRing R] {t : R}
    (C : FinitePrincipalPartsControl R M Q)
    (hTorsion : IsLocallyPowerTorsion R M t)
    (hUnbounded : HasUnboundedPowerTorsion R M t) :
    False :=
  (not_moduleFinite_of_unboundedPowerTorsion R M hTorsion hUnbounded)
    C.source_finite

end FinitePrincipalPartsControl

end

end CollisionIdeals.Planar
