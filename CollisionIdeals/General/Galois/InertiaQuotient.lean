import CollisionIdeals.General.Galois.Sheets
import Mathlib.GroupTheory.Index

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {G : Type u} [Group G]

/--
The relative inertia index attached to subgroups `I,H ≤ G`:

`e_H(I) = [I : I ∩ H]`.

In a Galois tower, `I` is an inertia subgroup and `H` fixes an
intermediate field.  The definition itself is dimension-independent.
-/
noncomputable def inertiaQuotientIndex
    (I H : Subgroup G) : ℕ :=
  H.relIndex I

/-- Lagrange's identity `e_H(I) · |I ∩ H| = |I|`. -/
theorem inertiaQuotientIndex_mul_card_intersection
    (I H : Subgroup G) :
    inertiaQuotientIndex I H *
        Nat.card (H.subgroupOf I) =
      Nat.card I := by
  exact Subgroup.index_mul_card _

/-- The relative inertia index is one exactly when `I ≤ H`. -/
theorem inertiaQuotientIndex_eq_one_iff
    (I H : Subgroup G) :
    inertiaQuotientIndex I H = 1 ↔ I ≤ H := by
  exact Subgroup.relIndex_eq_one

/-- If `I` is not contained in `H`, the relative inertia index is not one. -/
theorem inertiaQuotientIndex_ne_one
    (I H : Subgroup G)
    (hI : ¬ I ≤ H) :
    inertiaQuotientIndex I H ≠ 1 :=
  mt (inertiaQuotientIndex_eq_one_iff I H).mp hI

/-- In a finite group, `I ⊈ H` makes the relative inertia index greater than one. -/
theorem one_lt_inertiaQuotientIndex
    [Finite G]
    (I H : Subgroup G)
    (hI : ¬ I ≤ H) :
    1 < inertiaQuotientIndex I H := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  constructor
  · change (H.subgroupOf I).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  · exact inertiaQuotientIndex_ne_one I H hI

/--
For a core-free intermediate subgroup, every nontrivial inertia subgroup
has nontrivial relative index on at least one conjugate sheet.

This is the dimension-independent group-theoretic content of the
double-coset ramification argument.
-/
theorem exists_conjugate_one_lt_inertiaQuotientIndex
    [Finite G]
    (I H : Subgroup G)
    (hcore : H.normalCore = ⊥)
    (hI : I ≠ ⊥) :
    ∃ g : G,
      1 <
        inertiaQuotientIndex I
          (H.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨s, hs⟩ :=
    exists_sheet_moved_of_normalCore_eq_bot
      I H hcore hI
  revert hs
  refine Quotient.inductionOn s ?_
  intro g hs
  have hnot :
      ¬ I ≤ H.map (MulAut.conj g).toMonoidHom := by
    intro hle
    apply hs
    simpa using
      (inertiaInvisibleAt_conjugateSheet_iff I H g).2 hle
  exact
    ⟨g,
      one_lt_inertiaQuotientIndex
        I (H.map (MulAut.conj g).toMonoidHom) hnot⟩

end

end CollisionIdeals
