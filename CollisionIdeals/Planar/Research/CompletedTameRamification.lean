import CollisionIdeals.Planar.Research.LogarithmicInertia
import CollisionIdeals.Planar.NormalizationDiagram
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Completed tame parameters at a planar ramification divisor

This file connects the local logarithmic-inertia calculation to an actual
ramified height-one point in the planar normalization diagram.  The
completion and tame-parameter theorem are exposed as an explicit local
realization: mathlib currently supplies discrete valuation rings and inertia
groups, but not the general completed tame Kummer normal form needed to
construct this realization automatically.

The realization remembers enough of the geometric origin to avoid treating
the local calculation as free-standing data:

* the source valuation ring is the one attached to a specified ramified point
  `E` by the normalization diagram;
* its embedding into the local field reflects the completed valuation ring;
* the branch parameter comes from the planar base function field;
* the chosen inertia action extends a generator of the actual inertia group
  at `E`; and
* the local equation has the tame form `s = u * t ^ e`, with `t` a genuine
  uniformizer.

No planar moving-sheet coverage or boundary rigidity is asserted here.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]
variable {C : Type} [Field C] [CharZero C] [Algebra ℚ C]

open LogarithmicInertia

/--
The algebraic data from a completed tame local theorem at one actual
ramified height-one point `E` of a planar normalization diagram.

The carrier `C` is intended to be the completed normal function field at
`E`.  Rather than building a particular topological completion into the API,
the structure records precisely the valuation-preserving embedding and the
completed DVR data used by the logarithmic calculation.
-/
structure CompletedTameRamificationData
    (D : NormalizationDiagram (F := F) (N := N))
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (C : Type) [Field C] [CharZero C] [Algebra ℚ C] where
  completionMap : N →+* C
  completedValuationRing : ValuationSubring C
  completedDiscrete : IsDiscreteValuationRing completedValuationRing
  completionMap_mem_iff :
    ∀ x : N,
      completionMap x ∈ completedValuationRing ↔
        x ∈ (D.valuationAt E).valuationRing
  derivation : Derivation ℚ C C
  inertiaGenerator :
    inertiaGroupAt (PlanarBaseFunctionField F)
      (D.valuationAt E).valuationRing
  inertiaGenerator_generates :
    Subgroup.zpowers inertiaGenerator = ⊤
  inertiaAction : C ≃+* C
  inertiaAction_completionMap :
    ∀ x : N,
      inertiaAction (completionMap x) =
        completionMap (inertiaGenerator.1 x)
  inertiaAction_mem_iff :
    ∀ x : C,
      inertiaAction x ∈ completedValuationRing ↔
        x ∈ completedValuationRing
  baseBranchParameter : PlanarBaseFunctionField F
  unit : completedValuationRingˣ
  uniformizer : completedValuationRing
  uniformizer_irreducible : Irreducible uniformizer
  inertiaScalar : C
  ramificationIndex : ℕ
  one_lt_ramificationIndex : 1 < ramificationIndex
  ramificationIndex_eq_orderOf :
    ramificationIndex = orderOf inertiaGenerator
  branch_eq :
    completionMap
        (algebraMap (PlanarBaseFunctionField F) N baseBranchParameter) =
      ((unit : completedValuationRing) : C) *
        (uniformizer : C) ^ ramificationIndex
  derivation_branch :
    derivation
        (completionMap
          (algebraMap (PlanarBaseFunctionField F) N baseBranchParameter)) =
      completionMap
        (algebraMap (PlanarBaseFunctionField F) N baseBranchParameter)
  inertia_uniformizer :
    inertiaAction (uniformizer : C) =
      inertiaScalar * (uniformizer : C)
  inertiaScalar_pow :
    inertiaScalar ^ ramificationIndex = 1

namespace CompletedTameRamificationData

variable
    {D : NormalizationDiagram (F := F) (N := N)}
    {E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)}
    (T : CompletedTameRamificationData D E C)

/-- The selected inertia element is genuinely nontrivial. -/
theorem inertiaGenerator_ne_one : T.inertiaGenerator ≠ 1 := by
  intro h
  have hOrder : orderOf T.inertiaGenerator = 1 := by simp [h]
  have : T.ramificationIndex = 1 :=
    T.ramificationIndex_eq_orderOf.trans hOrder
  exact (Nat.ne_of_gt T.one_lt_ramificationIndex) this

/--
Forget the point-indexed completion data and retain the local tame parameter
package consumed by the logarithmic-inertia calculation.
-/
def toTameParameterData : TameParameterData C where
  derivation := T.derivation
  inertiaAction := T.inertiaAction
  branchParameter :=
    T.completionMap
      (algebraMap (PlanarBaseFunctionField F) N T.baseBranchParameter)
  unit := ((T.unit : T.completedValuationRing) : C)
  uniformizer := (T.uniformizer : C)
  inertiaScalar := T.inertiaScalar
  ramificationIndex := T.ramificationIndex
  ramificationIndex_pos := Nat.zero_lt_of_lt T.one_lt_ramificationIndex
  unit_ne_zero := by simp
  uniformizer_ne_zero := by
    exact_mod_cast T.uniformizer_irreducible.ne_zero
  branch_eq := T.branch_eq
  derivation_branch := T.derivation_branch
  inertia_uniformizer := T.inertia_uniformizer
  inertiaScalar_pow := T.inertiaScalar_pow

/-- The completed local derivation is logarithmic at the actual uniformizer. -/
theorem derivation_isLogarithmicAt :
    LogarithmicInertia.IsLogarithmicAt
      T.derivation (T.uniformizer : C)
      T.toTameParameterData.logarithmicWeight :=
  T.toTameParameterData.derivation_isLogarithmicAt

/--
The point-indexed inertia action has the expected character on every
negative-power principal part of the completed uniformizer.
-/
theorem inertia_apply_inv_pow (n : ℕ) :
    T.inertiaAction (((T.uniformizer : C) ^ n)⁻¹) =
      (T.inertiaScalar ^ n)⁻¹ * ((T.uniformizer : C) ^ n)⁻¹ :=
  T.toTameParameterData.inertia_apply_inv_pow' n

end CompletedTameRamificationData

end

end CollisionIdeals.Planar
