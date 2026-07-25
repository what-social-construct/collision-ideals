import CollisionIdeals.InertiaQuotient
import CollisionIdeals.Planar.Normalization

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/--
The finite normalized cover attached to one planar function-field tower.

The three geometric properties are recorded explicitly: mathlib constructs
the integral closures and all canonical maps unconditionally, while their
module-finiteness and the open-immersion assertion are separate inputs.
-/
structure PlanarNormalizedCover where
  normalClosure : PlanarNormalClosureData F N
  finiteIntermediateModel : IsPlanarFiniteCompletion F
  finiteNormalClosureModel :
    IsPlanarFiniteNormalizationInExtension (F := F) (N := N)
  intermediateOpen : IsPlanarIntermediateOpen F

/--
An abstract interface for candidate ramification divisors on `Z` and their
nontrivial inertia groups.

The fields below do not themselves certify codimension one or prove that
`inertiaGroup E` is the geometric inertia group at `centerOnZ E`; that
valuation-theoretic realization is a separate bridge.
-/
structure PlanarInertiaDivisorData
    (M : PlanarNormalizedCover (F := F) (N := N)) where
  RamificationDivisor : Type
  centerOnZ :
    RamificationDivisor →
      planarNormalizationInExtension (F := F) (N := N)
  inertiaGroup :
    RamificationDivisor →
      Subgroup M.normalClosure.galoisGroup
  inertia_nontrivial :
    ∀ E, inertiaGroup E ≠ ⊥

namespace PlanarInertiaDivisorData

variable {M : PlanarNormalizedCover (F := F) (N := N)}

/-- The center of a ramification divisor on the intermediate normalization `X̄`. -/
def centerOnFiniteCompletion
    (I : PlanarInertiaDivisorData M)
    (E : I.RamificationDivisor) :
    planarFiniteCompletion F :=
  (planarNormalClosureModelToFiniteCompletion M.normalClosure).base
    (I.centerOnZ E)

/--
The relative inertia index associated with the marked intermediate
subgroup.

For `H = Gal(N/L)` and inertia `I_E`, `H.relIndex I_E` is the index
`[I_E : I_E ∩ H]`, hence the group-theoretic form of
`|I_E| / |I_E ∩ H|`.  Identifying this group-theoretic number with the
geometric ramification index is a separate valuation-tower bridge.
-/
noncomputable def intermediateInertiaIndex
    (I : PlanarInertiaDivisorData M)
    (E : I.RamificationDivisor) : ℕ :=
  inertiaQuotientIndex
    (I.inertiaGroup E)
    M.normalClosure.intermediateFixingSubgroup

/--
Lagrange's identity for the relative subgroup index:

`[I_E : I_E ∩ H] · |I_E ∩ H| = |I_E|`.

The subtype `H.subgroupOf I_E` is the intersection `I_E ∩ H` viewed as a
subgroup of `I_E`.
-/
theorem intermediateInertiaIndex_mul_card_intersection
    (I : PlanarInertiaDivisorData M)
    (E : I.RamificationDivisor) :
    I.intermediateInertiaIndex E *
        Nat.card
          (M.normalClosure.intermediateFixingSubgroup.subgroupOf
            (I.inertiaGroup E)) =
      Nat.card (I.inertiaGroup E) := by
  exact
    inertiaQuotientIndex_mul_card_intersection
      (I.inertiaGroup E)
      M.normalClosure.intermediateFixingSubgroup

/-- The relative index is one exactly when `I_E ≤ H = Gal(N/L)`. -/
theorem intermediateInertiaIndex_eq_one_iff
    (I : PlanarInertiaDivisorData M)
    (E : I.RamificationDivisor) :
    I.intermediateInertiaIndex E = 1 ↔
      I.inertiaGroup E ≤
        M.normalClosure.intermediateFixingSubgroup := by
  exact
    inertiaQuotientIndex_eq_one_iff
      (I.inertiaGroup E)
      M.normalClosure.intermediateFixingSubgroup

/-- If `I_E` is not contained in `H`, the relative index is not one. -/
theorem intermediateInertiaIndex_ne_one
    (I : PlanarInertiaDivisorData M)
    (E : I.RamificationDivisor)
    (hE :
      ¬ I.inertiaGroup E ≤
        M.normalClosure.intermediateFixingSubgroup) :
    I.intermediateInertiaIndex E ≠ 1 := by
  exact
    inertiaQuotientIndex_ne_one
      (I.inertiaGroup E)
      M.normalClosure.intermediateFixingSubgroup
      hE

/-- In the finite Galois group, `I_E ⊈ H` makes the relative index greater than one. -/
theorem one_lt_intermediateInertiaIndex
    (I : PlanarInertiaDivisorData M)
    (E : I.RamificationDivisor)
    (hE :
      ¬ I.inertiaGroup E ≤
        M.normalClosure.intermediateFixingSubgroup) :
    1 < I.intermediateInertiaIndex E := by
  letI : Finite M.normalClosure.galoisGroup :=
    M.normalClosure.finiteGaloisGroup
  exact
    one_lt_inertiaQuotientIndex
      (I.inertiaGroup E)
      M.normalClosure.intermediateFixingSubgroup
      hE

/--
Every nontrivial inertia subgroup is visible on at least one conjugate
generic sheet.

This is the planar specialization of the dimension-independent core-free
group theorem.  It does not yet identify the conjugate subgroup with a
geometric conjugate model or the center of a valuation on its boundary.
-/
theorem exists_conjugate_one_lt_intermediateInertiaIndex
    (I : PlanarInertiaDivisorData M)
    (E : I.RamificationDivisor) :
    ∃ g : M.normalClosure.galoisGroup,
      1 <
        inertiaQuotientIndex
          (I.inertiaGroup E)
          (M.normalClosure.intermediateFixingSubgroup.map
            (MulAut.conj g).toMonoidHom) := by
  letI : Finite M.normalClosure.galoisGroup :=
    M.normalClosure.finiteGaloisGroup
  exact
    exists_conjugate_one_lt_inertiaQuotientIndex
      (I.inertiaGroup E)
      M.normalClosure.intermediateFixingSubgroup
      M.normalClosure.intermediateFixingSubgroup_normalCore_eq_bot
      (I.inertia_nontrivial E)

/--
The predicate expressing the expected boundary consequence: every divisor
that ramifies in the marked intermediate extension has its center deleted
from the affine-plane sheet.

It only concerns inertia groups not contained in `H`; inertia contained in
`H` is invisible in `L / K`.  This module does not derive the predicate
from étaleness; that implication is isolated in `Planar.EtaleBoundary`.
-/
def AllIntermediateRamificationHiddenInBoundary
    (I : PlanarInertiaDivisorData M) : Prop :=
  ∀ E,
    (¬ I.inertiaGroup E ≤
      M.normalClosure.intermediateFixingSubgroup) →
        I.centerOnFiniteCompletion E ∈
          planarFiniteCompletionBoundary F

/--
The normalized-cover version of the remaining planar rigidity assertion:
if all ramification visible in `L / K` is hidden in the deleted boundary,
then the canonical extension `K ⊂ L` is trivial.

This definition records the target for one supplied family; it does not
assert that the family is nonempty, exhaustive, or valuation-theoretically
realized.  Those facts must be supplied before this predicate represents
the global planar statement.
-/
def NormalizedHiddenInertiaRigidity
    (I : PlanarInertiaDivisorData M) : Prop :=
  AllIntermediateRamificationHiddenInBoundary I →
    PlanarFunctionFieldExtensionTrivial F

/--
Normalized hidden-inertia rigidity rules out a nontrivial marked
function-field extension.
-/
theorem functionFieldExtension_trivial_of_hiddenInertiaRigidity
    (I : PlanarInertiaDivisorData M)
    (hRigidity : NormalizedHiddenInertiaRigidity I)
    (hHidden :
      AllIntermediateRamificationHiddenInBoundary I) :
    PlanarFunctionFieldExtensionTrivial F :=
  hRigidity hHidden

end PlanarInertiaDivisorData

end

end CollisionIdeals
