import CollisionIdeals.Planar.Inertia
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/--
For a valuation ring `A ⊂ N`, the inclusion of its restriction to
`K = ℂ(P,Q)` into `A`.
-/
def valuationSubringComapInclusion
    (A : ValuationSubring N) :
    A.comap (algebraMap (PlanarBaseFunctionField F) N) →+* A where
  toFun x :=
    ⟨algebraMap (PlanarBaseFunctionField F) N x.1, x.2⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp

/--
The ramification index of the maximal ideals in the restricted valuation
ring tower.
-/
noncomputable def valuationRamificationIndex
    (A : ValuationSubring N) : ℕ :=
  Ideal.ramificationIdx
    (valuationSubringComapInclusion (F := F) A)
    (IsLocalRing.maximalIdeal
      (A.comap
        (algebraMap (PlanarBaseFunctionField F) N)))
    (IsLocalRing.maximalIdeal A)

/-- The actual decomposition subgroup stabilizing a valuation ring of `N`. -/
abbrev planarDecompositionGroupAt
    (_D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :
    Subgroup (N ≃ₐ[PlanarBaseFunctionField F] N) :=
  A.decompositionSubgroup (PlanarBaseFunctionField F)

/--
The actual inertia subgroup, obtained as the kernel of the decomposition
group action on the residue field and then included into `Gal(N/K)`.
-/
def planarInertiaGroupAt
    (_D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :
    Subgroup (N ≃ₐ[PlanarBaseFunctionField F] N) :=
  (A.inertiaSubgroup (PlanarBaseFunctionField F)).map
    (A.decompositionSubgroup
      (PlanarBaseFunctionField F)).subtype

/-- The inertia subgroup is contained in the decomposition subgroup. -/
theorem planarInertiaGroupAt_le_decompositionGroup
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :
    planarInertiaGroupAt D A ≤
      planarDecompositionGroupAt D A :=
  Subgroup.map_subtype_le _

/-- Inclusion into the full Galois group does not change the inertia order. -/
theorem card_planarInertiaGroupAt
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :
    Nat.card (planarInertiaGroupAt D A) =
      Nat.card
        (A.inertiaSubgroup
          (PlanarBaseFunctionField F)) := by
  exact
    Nat.card_congr
      (Subgroup.equivMapOfInjective
        (A.inertiaSubgroup
          (PlanarBaseFunctionField F))
        (A.decompositionSubgroup
          (PlanarBaseFunctionField F)).subtype
        (A.decompositionSubgroup
          (PlanarBaseFunctionField F)).subtype_injective).symm.toEquiv

/--
A discrete valuation ring of `N` whose restriction to `K` is also
discrete.  This is the valuation-theoretic portion of a codimension-one
divisor tower; scheme-theoretic centers are supplied separately.
-/
structure PlanarDiscreteValuationTower
    (_D : PlanarNormalClosureData F N) where
  valuationRing : ValuationSubring N
  topDiscrete :
    IsDiscreteValuationRing valuationRing
  baseDiscrete :
    IsDiscreteValuationRing
      (valuationRing.comap
        (algebraMap (PlanarBaseFunctionField F) N))

/--
The first valuation-theoretic bridge: for a geometric divisorial tower
with the required residue-separability and defectlessness hypotheses, the
ramification index equals the order of its inertia group.

The current `PlanarDiscreteValuationTower` records only the two DVR
conditions, so this equality remains an explicit target rather than a
consequence of characteristic zero alone.
-/
def PlanarDiscreteValuationTower.InertiaCardinalityBridge
    {D : PlanarNormalClosureData F N}
    (V : PlanarDiscreteValuationTower D) : Prop :=
  valuationRamificationIndex (F := F) V.valuationRing =
    Nat.card (planarInertiaGroupAt D V.valuationRing)

/--
Under the inertia-cardinality bridge, genuine ramification index different
from one is equivalent to nontrivial inertia.
-/
theorem PlanarDiscreteValuationTower.ramificationIndex_ne_one_iff
    {D : PlanarNormalClosureData F N}
    (V : PlanarDiscreteValuationTower D)
    (hBridge : V.InertiaCardinalityBridge) :
    valuationRamificationIndex (F := F) V.valuationRing ≠ 1 ↔
      planarInertiaGroupAt D V.valuationRing ≠ ⊥ := by
  rw [hBridge, ne_eq, Subgroup.card_eq_one]

section Family

variable {M : PlanarNormalizedCover (F := F) (N := N)}

/--
A family of concrete discrete valuation towers supplying the inertia
subgroups used by the existing planar divisor interface.

The center field still needs a geometric theorem identifying it with the
center of the valuation on `Z`; only the inertia subgroup is constructed
here.
-/
structure PlanarValuationInertiaFamily
    (M : PlanarNormalizedCover (F := F) (N := N)) where
  Divisor : Type
  valuation :
    Divisor →
      PlanarDiscreteValuationTower M.normalClosure
  centerOnZ :
    Divisor →
      planarNormalizationInExtension (F := F) (N := N)
  inertia_nontrivial :
    ∀ E,
      planarInertiaGroupAt M.normalClosure
          (valuation E).valuationRing ≠ ⊥

/--
The concrete valuation family feeds the already-existing group-theoretic
quotient interface; no second relative-index definition is introduced.
-/
def PlanarValuationInertiaFamily.toInertiaDivisorData
    (V : PlanarValuationInertiaFamily M) :
    PlanarInertiaDivisorData M where
  RamificationDivisor := V.Divisor
  centerOnZ := V.centerOnZ
  inertiaGroup E :=
    planarInertiaGroupAt M.normalClosure
      (V.valuation E).valuationRing
  inertia_nontrivial := V.inertia_nontrivial

/--
The predicate that every valuation in the family satisfies the
inertia-cardinality bridge.
-/
def PlanarValuationInertiaFamily.HasInertiaCardinalityBridge
    (V : PlanarValuationInertiaFamily M) : Prop :=
  ∀ E, (V.valuation E).InertiaCardinalityBridge

end Family

end

end CollisionIdeals
