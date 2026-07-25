import CollisionIdeals.DecompositionSheets
import CollisionIdeals.Planar.ValuationInertia

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/-- The inertia kernel before inclusion into the full planar Galois group. -/
abbrev planarInertiaWithinDecomposition
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :
    Subgroup (planarDecompositionGroupAt D A) :=
  A.inertiaSubgroup (PlanarBaseFunctionField F)

set_option synthInstance.maxHeartbeats 100000 in
/-- Valuation inertia is normal in its decomposition subgroup because it is a kernel. -/
instance planarInertiaWithinDecomposition_normal
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :
    (planarInertiaWithinDecomposition D A).Normal := by
  unfold planarInertiaWithinDecomposition
    ValuationSubring.inertiaSubgroup
  infer_instance

/--
The double-coset classes `D_E \ G / H` attached to one planar valuation.

With the convention that the representative `g` corresponds to the
contraction of `g⁻¹E` to `N^H`, valuation theory identifies these classes
with the prime divisors of the intermediate normalization above the base
divisor.  That prime-classification equivalence is not asserted here.
-/
abbrev PlanarDecompositionSheetClasses
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :=
  DecompositionSheetClasses
    (planarDecompositionGroupAt D A)
    D.intermediateFixingSubgroup

/-- The well-defined relative inertia index on a planar double-coset class. -/
noncomputable def planarInertiaIndexAtDoubleCoset
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N) :
    PlanarDecompositionSheetClasses D A → ℕ :=
  inertiaIndexAtDoubleCoset
    (planarDecompositionGroupAt D A)
    (planarInertiaWithinDecomposition D A)
    D.intermediateFixingSubgroup

/-- On the class represented by `g`, the index is `[I_E : I_E ∩ gHg⁻¹]`. -/
@[simp]
theorem planarInertiaIndexAtDoubleCoset_mk
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N)
    (g : D.galoisGroup) :
    planarInertiaIndexAtDoubleCoset D A
        (DoubleCoset.mk
          (planarDecompositionGroupAt D A)
          D.intermediateFixingSubgroup g) =
      inertiaQuotientIndex
        (planarInertiaGroupAt D A)
        (D.intermediateFixingSubgroup.map
          (MulAut.conj g).toMonoidHom) := by
  rw [planarInertiaIndexAtDoubleCoset,
    inertiaIndexAtDoubleCoset_mk]
  rfl

/--
Nontrivial planar valuation inertia has index greater than one on at least
one double-coset class of the intermediate normal-closure sheet space.

The conclusion becomes the existence of an actual ramified prime divisor
after supplying the standard prime/double-coset classification.
-/
theorem exists_planarDoubleCoset_one_lt_inertiaIndex
    (D : PlanarNormalClosureData F N)
    (A : ValuationSubring N)
    (hI : planarInertiaGroupAt D A ≠ ⊥) :
    ∃ q : PlanarDecompositionSheetClasses D A,
      1 < planarInertiaIndexAtDoubleCoset D A q := by
  letI : Finite D.galoisGroup :=
    D.finiteGaloisGroup
  have hWithin :
      planarInertiaWithinDecomposition D A ≠ ⊥ := by
    intro hbot
    apply hI
    change
      (A.inertiaSubgroup
        (PlanarBaseFunctionField F)).map
          (A.decompositionSubgroup
            (PlanarBaseFunctionField F)).subtype = ⊥
    change
      A.inertiaSubgroup
        (PlanarBaseFunctionField F) = ⊥ at hbot
    rw [hbot, Subgroup.map_bot]
  exact
    exists_doubleCoset_one_lt_inertiaIndex
      (planarDecompositionGroupAt D A)
      (planarInertiaWithinDecomposition D A)
      D.intermediateFixingSubgroup
      D.intermediateFixingSubgroup_normalCore_eq_bot
      hWithin

end

end CollisionIdeals
