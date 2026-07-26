import CollisionIdeals.Planar.DecompositionSheets
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Unramified.Locus

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

open AlgebraicGeometry CategoryTheory

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/--
The finite normal-closure model has no ramification at any height-one
prime.

This is the concrete local input consumed by branch purity.  It quantifies
over the actual codimension-one points of the normalization ring rather
than over an arbitrary family of valuation witnesses.
-/
def NoCodimensionOneRamification : Prop :=
  letI : Algebra (planarImageAlgebra F) N :=
    planarNormalClosureBaseAlgebra (F := F) (N := N)
  ∀ q :
      PrimeSpectrum
        (PlanarNormalizationInExtensionRing (F := F) (N := N)),
    q.asIdeal.primeHeight = 1 →
      Algebra.IsUnramifiedAt
        (planarImageAlgebra F) q.asIdeal

/--
An actual height-one point of the normalization at which the local
extension is ramified.

Indexing the normalization diagram by this subtype makes exhaustiveness
formal: proving this type empty is exactly proving
`NoCodimensionOneRamification`.
-/
def RamifiedCodimensionOnePoint :=
  letI : Algebra (planarImageAlgebra F) N :=
    planarNormalClosureBaseAlgebra (F := F) (N := N)
  { q :
      PrimeSpectrum
        (PlanarNormalizationInExtensionRing (F := F) (N := N)) //
      q.asIdeal.primeHeight = 1 ∧
        ¬ Algebra.IsUnramifiedAt
          (planarImageAlgebra F) q.asIdeal }

/--
A discrete valuation tower is centered at `q` when its valuation ring
contains the normalization ring and its maximal ideal contracts to `q`.

This compatibility ties the valuation-theoretic inertia group to the
indicated point of `Z = Norm_N(Y)`.
-/
def ValuationCenteredAt
    {D : PlanarNormalClosureData F N}
    (V : PlanarDiscreteValuationTower D)
    (q :
      PrimeSpectrum
        (PlanarNormalizationInExtensionRing (F := F) (N := N))) : Prop :=
  ∃ centerMap :
      PlanarNormalizationInExtensionRing (F := F) (N := N) →+*
        V.valuationRing,
    (∀ x,
      ((centerMap x : V.valuationRing) : N) = (x : N)) ∧
      (IsLocalRing.maximalIdeal V.valuationRing).comap centerMap =
        q.asIdeal

/--
The finite normalization triangle together with the pointwise realization
of its conjugate sheets.

For every genuinely ramified height-one point `E` of `Z`, the diagram
records:

* a divisorial valuation centered at `E`;
* the resulting nontrivial inertia subgroup;
* a center on `X̄` for every double-coset class `D_E \ G / H`;
* compatibility of those centers with the maps to `Y`;
* identification of the identity class with the marked contraction
  `Z ⟶ X̄`.

It contains no étale visibility theorem and no global planar boundary
rigidity theorem.  Those are the two separate predicates below.
-/
structure NormalizationDiagram where
  cover : PlanarNormalizedCover (F := F) (N := N)
  valuationAt :
    RamifiedCodimensionOnePoint (F := F) (N := N) →
      PlanarDiscreteValuationTower cover.normalClosure
  valuation_centered :
    ∀ E, ValuationCenteredAt (valuationAt E) E.1
  inertia_nontrivial :
    ∀ E,
      planarInertiaGroupAt cover.normalClosure
          (valuationAt E).valuationRing ≠ ⊥
  centerAtClass :
    ∀ E,
      PlanarDecompositionSheetClasses cover.normalClosure
          (valuationAt E).valuationRing →
        planarFiniteCompletion F
  centerAtClass_mapsToBase :
    ∀ E q,
      (planarFiniteCompletionToBase F).base
          (centerAtClass E q) =
        (planarNormalizationInExtensionToBase
          (F := F) (N := N)).base E.1
  baseClass_center :
    ∀ E,
      centerAtClass E
          (DoubleCoset.mk
            (planarDecompositionGroupAt cover.normalClosure
              (valuationAt E).valuationRing)
            cover.normalClosure.intermediateFixingSubgroup
            1) =
        (planarNormalClosureModelToFiniteCompletion
          cover.normalClosure).base E.1

namespace NormalizationDiagram

variable (D : NormalizationDiagram (F := F) (N := N))

/-- The normal-closure leg `Z ⟶ X̄` of the packaged diagram. -/
def toIntermediate :
    planarNormalizationInExtension (F := F) (N := N) ⟶
      planarFiniteCompletion F :=
  planarNormalClosureModelToFiniteCompletion D.cover.normalClosure

/-- The finite normalization leg `Z ⟶ Y` of the packaged diagram. -/
def toBase (_D : NormalizationDiagram (F := F) (N := N)) :
    planarNormalizationInExtension (F := F) (N := N) ⟶
      Spec (.of (planarImageAlgebra F)) :=
  planarNormalizationInExtensionToBase (F := F) (N := N)

/-- The packaged normalization triangle `Z ⟶ X̄ ⟶ Y` commutes. -/
theorem triangle :
    D.toIntermediate ≫ planarFiniteCompletionToBase F =
      D.toBase :=
  planarNormalClosureModelToFiniteCompletion_comp_toBase
    D.cover.normalClosure

/-- The double-coset classes indexing conjugate centers above one point. -/
abbrev sheetClasses
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :=
  PlanarDecompositionSheetClasses D.cover.normalClosure
    (D.valuationAt E).valuationRing

/-- The inertia subgroup attached to one actual ramified height-one point. -/
abbrev inertiaGroup
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    Subgroup D.cover.normalClosure.galoisGroup :=
  planarInertiaGroupAt D.cover.normalClosure
    (D.valuationAt E).valuationRing

/--
The diagram supplies an exhaustive valuation-inertia family indexed by
the actual ramified height-one points.

This is the compatibility adapter to the older arbitrary-family API.  Its
indexing type is canonical, so emptiness of this family has the intended
codimension-one meaning.
-/
def toValuationInertiaFamily :
    PlanarValuationInertiaFamily D.cover where
  Divisor :=
    RamifiedCodimensionOnePoint (F := F) (N := N)
  valuation := D.valuationAt
  centerOnZ E := E.1
  inertia_nontrivial := D.inertia_nontrivial

/-- Forget further to the existing abstract inertia-divisor interface. -/
def toInertiaDivisorData :
    PlanarInertiaDivisorData D.cover :=
  D.toValuationInertiaFamily.toInertiaDivisorData

@[simp]
theorem toValuationInertiaFamily_centerOnZ
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.toValuationInertiaFamily.centerOnZ E = E.1 :=
  rfl

@[simp]
theorem toValuationInertiaFamily_valuation
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.toValuationInertiaFamily.valuation E =
      D.valuationAt E :=
  rfl

@[simp]
theorem toInertiaDivisorData_inertiaGroup
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.toInertiaDivisorData.inertiaGroup E =
      D.inertiaGroup E :=
  rfl

/-- The relative inertia index of one conjugate center. -/
noncomputable def inertiaIndex
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.sheetClasses E → ℕ :=
  planarInertiaIndexAtDoubleCoset D.cover.normalClosure
    (D.valuationAt E).valuationRing

/-- One conjugate center remains visible in the affine-plane open sheet. -/
def ConjugateCenterVisible
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) : Prop :=
  D.centerAtClass E q ∈
    Set.range (planarSourceToFiniteCompletion F).base

/--
The pointwise visible-conjugate-sheet inertia statement at one
double-coset class.

If the affine-plane sheet is étale over the base and this conjugate center
remains in the affine open, its relative inertia index is one.
-/
def VisibleConjugateSheetInertiaAt
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) : Prop :=
  IsEtale (planarSourceToImageBase F) →
    D.ConjugateCenterVisible E q →
      D.inertiaIndex E q = 1

/--
The local normalization/valuation adapter at every ramified point and
every existing double-coset class.  It is not the later global boundary
theorem.
-/
def VisibleConjugateSheetInertia : Prop :=
  ∀ E q, D.VisibleConjugateSheetInertiaAt E q

/--
The specifically planar global boundary-rigidity statement.

For each actual ramified point, if every conjugate center with positive
relative inertia index lies in the deleted boundary, then the actual
inertia subgroup is trivial.  This is deliberately independent of the
preceding pointwise étale/visibility predicate.
-/
def PlanarBoundaryRigidity : Prop :=
  ∀ E,
    (∀ q : D.sheetClasses E,
      D.inertiaIndex E q ≠ 1 →
        D.centerAtClass E q ∈
          planarFiniteCompletionBoundary F) →
      D.inertiaGroup E = ⊥

/--
The identity double-coset center is exactly the contraction along the
normalization leg `Z ⟶ X̄`.
-/
theorem centerAtBaseClass
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.centerAtClass E
        (DoubleCoset.mk
          (planarDecompositionGroupAt D.cover.normalClosure
            (D.valuationAt E).valuationRing)
          D.cover.normalClosure.intermediateFixingSubgroup
          1) =
      D.toIntermediate.base E.1 :=
  D.baseClass_center E

/-- Every packaged conjugate center lies over the image of `E` in `Y`. -/
theorem conjugateCenter_mapsToBase
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) :
    (planarFiniteCompletionToBase F).base
        (D.centerAtClass E q) =
      D.toBase.base E.1 :=
  D.centerAtClass_mapsToBase E q

/--
Nontrivial inertia moves at least one double-coset class, expressed as a
relative inertia index greater than one.
-/
theorem exists_one_lt_inertiaIndex
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    ∃ q : D.sheetClasses E,
      1 < D.inertiaIndex E q :=
  exists_planarDoubleCoset_one_lt_inertiaIndex
    D.cover.normalClosure
    (D.valuationAt E).valuationRing
    (D.inertia_nontrivial E)

/--
Pointwise visible-sheet étaleness sends every positive-index conjugate
center into the deleted boundary.
-/
theorem ramifiedCenter_mem_boundary
    (hVisible : D.VisibleConjugateSheetInertia)
    (hEtale : IsEtale (planarSourceToImageBase F))
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hq : D.inertiaIndex E q ≠ 1) :
    D.centerAtClass E q ∈
      planarFiniteCompletionBoundary F := by
  change
    D.centerAtClass E q ∉
      Set.range (planarSourceToFiniteCompletion F).base
  intro hInOpen
  exact hq (hVisible E q hEtale hInOpen)

/--
The local visible-sheet theorem and the later global planar boundary
theorem force the actual inertia at each ramified point to vanish.
-/
theorem inertiaGroup_eq_bot
    (hVisible : D.VisibleConjugateSheetInertia)
    (hBoundary : D.PlanarBoundaryRigidity)
    (hEtale : IsEtale (planarSourceToImageBase F))
    (E : RamifiedCodimensionOnePoint (F := F) (N := N)) :
    D.inertiaGroup E = ⊥ :=
  hBoundary E fun q hq ↦
    D.ramifiedCenter_mem_boundary hVisible hEtale E q hq

/--
The local and global inputs exclude every actual ramified height-one
point of the normalization.
-/
theorem ramifiedCodimensionOnePoint_isEmpty
    (hVisible : D.VisibleConjugateSheetInertia)
    (hBoundary : D.PlanarBoundaryRigidity)
    (hEtale : IsEtale (planarSourceToImageBase F)) :
    IsEmpty
      (RamifiedCodimensionOnePoint (F := F) (N := N)) := by
  constructor
  intro E
  exact
    D.inertia_nontrivial E
      (D.inertiaGroup_eq_bot hVisible hBoundary hEtale E)

/--
The exact local conclusion consumed later by branch purity: all
height-one points of the finite normalization are unramified.
-/
theorem noCodimensionOneRamification
    (hVisible : D.VisibleConjugateSheetInertia)
    (hBoundary : D.PlanarBoundaryRigidity)
    (hEtale : IsEtale (planarSourceToImageBase F)) :
    NoCodimensionOneRamification (F := F) (N := N) := by
  intro q hq
  by_contra hRamified
  let E :
      RamifiedCodimensionOnePoint (F := F) (N := N) :=
    ⟨q, hq, hRamified⟩
  exact
    (D.ramifiedCodimensionOnePoint_isEmpty
      hVisible hBoundary hEtale).false E

end NormalizationDiagram

end

end CollisionIdeals.Planar
