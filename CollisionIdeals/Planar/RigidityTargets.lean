import CollisionIdeals.BoundaryPrincipalParts
import CollisionIdeals.Planar.NormalizationDiagram
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Two planar finiteness criteria

This file names the two module-theoretic criteria used in the planar paper.
They are deliberately distinct from the finiteness already built into the
normalization diagram.

* `PlanarBoundaryCoherence F` says that the first local cohomology of the
  deleted Zariski--Main boundary is finite.  This is the global-boundary
  formulation: its geometric consequence is that the whole boundary is empty.
* `PlanarRamificationRigidity` says that the already finite module of relative
  Kähler differentials on the Galois normalization has finite length.  This is
  the divisorial formulation: its immediate geometric consequence is the
  absence of height-one ramification.

The local-cohomology comparison with sections on the affine open and the
finite-length/support comparison are substantive geometric bridges.  They are
not hidden in these definitions.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- The radical ideal of the deleted intermediate-normalization boundary. -/
def planarIntermediateBoundaryIdeal (F : PlanarPolynomialMap) :
    Ideal (PolynomialIntermediateNormalizationRing F) :=
  PrimeSpectrum.vanishingIdeal
    (polynomialIntermediateNormalizationBoundary F)

/--
The global-boundary criterion: first local cohomology of the deleted boundary is
finite over the intermediate normalization ring.
-/
def PlanarBoundaryCoherence (F : PlanarPolynomialMap) : Prop :=
  BoundaryCoherence (PolynomialIntermediateNormalizationRing F)
    (planarIntermediateBoundaryIdeal F)

/--
The explicit geometric bridge for the global-boundary route.  It is separate because
the open-complement local-cohomology sequence and the finite-open-immersion
argument are not yet formalized in the development.
-/
def BoundaryCoherenceBridge : Prop :=
  ∀ (F : PlanarPolynomialMap),
    PlanarBoundaryCoherence F →
      polynomialIntermediateNormalizationBoundary F = ∅

/--
The minimal planar ramification target: the module of relative differentials
of the common Galois normalization has finite length.

The normalization ring is already finite over the polynomial image algebra;
finite length is the additional assertion that the differential module has
zero-dimensional support.
-/
def PlanarRamificationRigidity : Prop := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  let T := PolynomialNormalizationInExtensionRing (F := F) (N := N)
  let B := PolynomialImageAlgebra F
  letI : Algebra B T := inferInstance
  letI : SMulCommClass B T T :=
    ⟨fun b x y => by simp only [Algebra.smul_def]; ring⟩
  letI : Module T (KaehlerDifferential B T) :=
    KaehlerDifferential.module' (R := B) (S := T) (R' := T)
  exact
    IsFiniteLength T (KaehlerDifferential B T)

/--
The precise bridge from the finite-length target to the input consumed by
purity.  It is named separately because the required support theorem for
Kähler differentials is not presently supplied by the formal development.
-/
def RamificationRigidityBridge : Prop :=
  ∀ {F : PlanarPolynomialMap}
    {N : Type} [Field N]
    [Algebra (PlanarBaseFunctionField F) N]
    (_M : PlanarNormalizedCover (F := F) (N := N)),
      PlanarRamificationRigidity (F := F) (N := N) →
        NoCodimensionOneRamification (F := F) (N := N)

end

end CollisionIdeals.Planar
