import CollisionIdeals.Planar.DecompositionSheets
import CollisionIdeals.Planar.GenericFiber
import CollisionIdeals.Planar.Rigidity

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]
variable {M : PlanarNormalizedCover (F := F) (N := N)}
variable {V : PlanarValuationInertiaFamily M}

/--
The global existence input for an exhaustive inertia family: a nontrivial
planar function-field extension supplies at least one nontrivial
divisorial-inertia witness.

This is the purity/finite-étale alternative that remains separate from the
double-coset and visibility calculations.
-/
def PlanarValuationInertiaFamily.NontrivialExtensionHasDivisor
    (V : PlanarValuationInertiaFamily M) : Prop :=
  ¬ PlanarFunctionFieldExtensionTrivial F →
    Nonempty V.Divisor

/--
The group-theoretic shadow of the conjugate affine-plane opens on the
normal-closure model.

For each valuation divisor, `visibleSheets E` is the set of sheets whose
corresponding centers lie in their conjugate affine opens.  Étaleness then
makes inertia invisible on those sheets.

Constructing this set from actual scheme-theoretic centers and conjugate
open immersions is the remaining geometric boundary bridge.
-/
structure PlanarConjugateOpenVisibility
    (V : PlanarValuationInertiaFamily M) where
  visibleSheets :
    V.Divisor →
      Set
        (GaloisSheets
          M.normalClosure.intermediateFixingSubgroup)
  etale_visible :
    ∀ E,
      InertiaInvisibleOn
        (planarInertiaGroupAt M.normalClosure
          (V.valuation E).valuationRing)
        M.normalClosure.intermediateFixingSubgroup
        (visibleSheets E)

namespace PlanarConjugateOpenVisibility

variable (W : PlanarConjugateOpenVisibility V)

/--
The exact global boundary condition: at each divisor, the visible sheets
have stabilizers whose intersection detects inertia.

An ordinary union cover is not by itself the needed statement.  This
detection condition is the group-theoretic form of the required global
overlap/coverage property of the conjugate affine opens.
-/
def DetectsInertia : Prop :=
  ∀ E,
    VisibleSheetsDetectInertia
      M.normalClosure.intermediateFixingSubgroup
      (W.visibleSheets E)

/-- The stronger sufficient condition that every conjugate sheet is visible. -/
def AllSheetsVisible : Prop :=
  ∀ E, W.visibleSheets E = Set.univ

/--
If every conjugate center remains in its affine open, core-freeness makes
the visible sheets detect inertia.
-/
theorem detectsInertia_of_allSheetsVisible
    (hAll : W.AllSheetsVisible) :
    W.DetectsInertia := by
  intro E
  rw [hAll E]
  exact
    visibleSheetsDetectInertia_univ_of_normalCore_eq_bot
      M.normalClosure.intermediateFixingSubgroup
      M.normalClosure.intermediateFixingSubgroup_normalCore_eq_bot

/--
The global detection condition contradicts the existence of any supplied
nontrivial ramification divisor.
-/
theorem divisor_isEmpty_of_detectsInertia
    (hDetect : W.DetectsInertia) :
    IsEmpty V.Divisor := by
  constructor
  intro E
  exact
    V.inertia_nontrivial E
      (hDetect E
        (planarInertiaGroupAt M.normalClosure
          (V.valuation E).valuationRing)
        (W.etale_visible E))

/--
In particular, an exhaustive nonempty family of nontrivial divisorial
inertia is incompatible with global conjugate-open detection.
-/
theorem false_of_detectsInertia
    [Nonempty V.Divisor]
    (hDetect : W.DetectsInertia) :
    False :=
  not_nonempty_iff.mpr
    (W.divisor_isEmpty_of_detectsInertia hDetect)
    inferInstance

/--
An exhaustive inertia family together with global conjugate-open detection
forces the planar function-field extension to be trivial.
-/
theorem functionFieldExtension_trivial_of_detectsInertia
    (hExists : V.NontrivialExtensionHasDivisor)
    (hDetect : W.DetectsInertia) :
    PlanarFunctionFieldExtensionTrivial F := by
  by_contra hNontrivial
  letI : Nonempty V.Divisor :=
    hExists hNontrivial
  exact W.false_of_detectsInertia hDetect

/--
After the generic-fiber bridge, the global boundary calculation returns
to the original ideal-theoretic obstruction.
-/
theorem obstructionIdeal_eq_bot_of_detectsInertia
    (hKeller : IsPlanarKeller F)
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal)
    (hExists : V.NontrivialExtensionHasDivisor)
    (hDetect : W.DetectsInertia) :
    obstructionIdeal F = ⊥ :=
  obstructionIdeal_eq_bot_of_planarFunctionField_trivial
    hGeneric F hKeller
      (W.functionFieldExtension_trivial_of_detectsInertia
        hExists hDetect)

end PlanarConjugateOpenVisibility

end

end CollisionIdeals
