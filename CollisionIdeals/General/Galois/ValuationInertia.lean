import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u v

variable
    (K : Type u) [Field K]
    {N : Type v} [Field N] [Algebra K N]

/-- The decomposition subgroup stabilizing a valuation ring of `N`. -/
abbrev decompositionGroupAt
    (A : ValuationSubring N) :
    Subgroup (N ≃ₐ[K] N) :=
  A.decompositionSubgroup K

/--
The inertia subgroup, obtained as the kernel of the decomposition-group
action on the residue field and then included into `Gal(N/K)`.
-/
def inertiaGroupAt
    (A : ValuationSubring N) :
    Subgroup (N ≃ₐ[K] N) :=
  (A.inertiaSubgroup K).map
    (A.decompositionSubgroup K).subtype

/-- The inertia subgroup is contained in the decomposition subgroup. -/
theorem inertiaGroupAt_le_decompositionGroup
    (A : ValuationSubring N) :
    inertiaGroupAt K A ≤ decompositionGroupAt K A :=
  Subgroup.map_subtype_le _

/--
The inertia kernel before inclusion into the full Galois group.

This is the valuation-theoretic subgroup supplied to the
dimension-independent double-coset construction.
-/
abbrev inertiaWithinDecomposition
    (A : ValuationSubring N) :
    Subgroup (decompositionGroupAt K A) :=
  A.inertiaSubgroup K

set_option synthInstance.maxHeartbeats 100000 in
/-- Valuation inertia is normal in its decomposition subgroup. -/
instance inertiaWithinDecomposition_normal
    (A : ValuationSubring N) :
    (inertiaWithinDecomposition K A).Normal := by
  unfold inertiaWithinDecomposition
    ValuationSubring.inertiaSubgroup
  infer_instance

/--
A discrete valuation ring of `N` whose restriction to `K` is also
discrete. This is the valuation-theoretic portion of a codimension-one
divisor tower; scheme-theoretic centers are supplied separately.
-/
structure DiscreteValuationTower where
  valuationRing : ValuationSubring N
  topDiscrete :
    IsDiscreteValuationRing valuationRing
  baseDiscrete :
    IsDiscreteValuationRing
      (valuationRing.comap (algebraMap K N))

end

end CollisionIdeals
