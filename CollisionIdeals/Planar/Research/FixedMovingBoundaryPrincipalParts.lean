import CollisionIdeals.Planar.BoundarySeparation
import CollisionIdeals.Planar.Research.PrincipalPartsStrategy

/-!
# Fixed--moving boundary principal parts

This research module combines the two canonical ideals used by planar
boundary separation:

* `fixedLocusIdeal C`, cutting out the locus fixed by a subgroup `C`; and
* `movingBoundaryIdeal B.boundaryIdeal C`, cutting out the common boundary
  of the conjugate affine sheets moved by `C`.

Their sum is the exact fixed--moving support ideal.  Its first local
cohomology is the prospective boundary contribution on which a
boundary-compatible secant projector would have to act.  The file proves
the ideal-theoretic and zero-locus dictionaries already available from the
current normalization model.  It does not assert the successive-support
spectral-sequence isomorphism, a DVR localization formula, an equivariant
character calculation, or secant--trace landing.
-/

set_option autoImplicit false

open CategoryTheory

namespace CollisionIdeals.Planar

noncomputable section

variable {F : PlanarPolynomialMap}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]
variable {D : NormalizationDiagram (F := F) (N := N)}

/--
The ideal cutting out the intersection of the `C`-fixed locus with the
boundaries of all conjugate affine sheets moved by `C`.
-/
def fixedMovingBoundarySupportIdeal
    (B : BoundaryIdealData D)
    (C : Subgroup (NormalizationGaloisGroup D)) :
    Ideal (GaloisNormalizationRing (F := F) (N := N)) :=
  fixedLocusIdeal C + movingBoundaryIdeal B.boundaryIdeal C

/--
First local cohomology with support in the fixed--moving boundary ideal.
This is the canonical combined-support object; identifying it with an
iterated fixed-support submodule of boundary principal parts is a separate
successive-support theorem.
-/
def FixedMovingBoundaryPrincipalParts
    (B : BoundaryIdealData D)
    (C : Subgroup (NormalizationGaloisGroup D)) :
    ModuleCat (GaloisNormalizationRing (F := F) (N := N)) :=
  CombinedSupportPrincipalParts
    (GaloisNormalizationRing (F := F) (N := N))
    (fixedLocusIdeal C) (movingBoundaryIdeal B.boundaryIdeal C)

/-- Containment of the combined support ideal is containment of both parts. -/
theorem fixedMovingBoundarySupportIdeal_le_iff
    (B : BoundaryIdealData D)
    (C : Subgroup (NormalizationGaloisGroup D))
    (I : Ideal (GaloisNormalizationRing (F := F) (N := N))) :
    fixedMovingBoundarySupportIdeal B C ≤ I ↔
      fixedLocusIdeal C ≤ I ∧ movingBoundaryIdeal B.boundaryIdeal C ≤ I := by
  simp [fixedMovingBoundarySupportIdeal]

/-- Fixed-locus ideals grow with the acting subgroup. -/
theorem fixedLocusIdeal_mono
    {C C' : Subgroup (NormalizationGaloisGroup D)}
    (h : C ≤ C') :
    fixedLocusIdeal C ≤ fixedLocusIdeal C' := by
  rw [fixedLocusIdeal_le_iff]
  intro σ t
  apply Ideal.subset_span
  exact ⟨⟨σ.1, h σ.2⟩, t, rfl⟩

/--
The zero locus of the moving-boundary sum is the intersection of the
individual boundaries of all sheets moved by `C`.
-/
theorem zeroLocus_movingBoundaryIdeal
    (B : BoundaryIdealData D)
    (C : Subgroup (NormalizationGaloisGroup D)) :
    PrimeSpectrum.zeroLocus
        (R := GaloisNormalizationRing (F := F) (N := N))
        (movingBoundaryIdeal (D := D) B.boundaryIdeal C) =
      ⋂ (g : NormalizationGaloisGroup D),
        ⋂ (_ : ¬ C ≤ D.cover.normalClosure.intermediateFixingSubgroup.map
          (MulAut.conj g).toMonoidHom),
          pulledBackConjugateBoundary D g := by
  simp [movingBoundaryIdeal, BoundaryIdealData.boundaryIdeal,
    PrimeSpectrum.zeroLocus_iSup,
    zeroLocus_pulledBackConjugateBoundaryIdeal]

/--
The combined support is exactly the fixed locus intersected with every
boundary belonging to a `C`-moving conjugate sheet.
-/
theorem zeroLocus_fixedMovingBoundarySupportIdeal
    (B : BoundaryIdealData D)
    (C : Subgroup (NormalizationGaloisGroup D)) :
    PrimeSpectrum.zeroLocus
        (R := GaloisNormalizationRing (F := F) (N := N))
        (fixedMovingBoundarySupportIdeal B C) =
      PrimeSpectrum.zeroLocus
          (R := GaloisNormalizationRing (F := F) (N := N))
          (fixedLocusIdeal (D := D) C) ∩
        ⋂ (g : NormalizationGaloisGroup D),
          ⋂ (_ : ¬ C ≤ D.cover.normalClosure.intermediateFixingSubgroup.map
            (MulAut.conj g).toMonoidHom),
            pulledBackConjugateBoundary D g := by
  rw [show PrimeSpectrum.zeroLocus
        (R := GaloisNormalizationRing (F := F) (N := N))
        (fixedMovingBoundarySupportIdeal B C) =
      PrimeSpectrum.zeroLocus
          (R := GaloisNormalizationRing (F := F) (N := N))
          (fixedLocusIdeal (D := D) C : Ideal _) ∩
      PrimeSpectrum.zeroLocus
          (R := GaloisNormalizationRing (F := F) (N := N))
          (movingBoundaryIdeal (D := D) B.boundaryIdeal C : Ideal _) by
        simp [fixedMovingBoundarySupportIdeal, PrimeSpectrum.zeroLocus_sup],
    zeroLocus_movingBoundaryIdeal]

/--
If `C` lies in the inertia group at a ramified divisor, then its entire
fixed--moving support ideal lies in the corresponding height-one prime.
-/
theorem fixedMovingBoundarySupportIdeal_le_ramifiedPrime
    (B : BoundaryIdealData D)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N))
    (C : Subgroup (NormalizationGaloisGroup D))
    (hC : C ≤ inertiaGroupAt (PlanarBaseFunctionField F)
      (D.valuationAt E).valuationRing) :
    fixedMovingBoundarySupportIdeal B C ≤ E.1.asIdeal := by
  rw [fixedMovingBoundarySupportIdeal_le_iff]
  exact ⟨
    (fixedLocusIdeal_mono hC).trans (B.fixedLocusIdeal_le E),
    movingBoundaryIdeal_le_ramifiedPrime
      B.ramificationRealization B.sourceEtale E C hC⟩

/-- The fixed--moving support attached to the actual inertia lies at its center. -/
theorem actualInertiaFixedMovingBoundarySupportIdeal_le
    (B : BoundaryIdealData D)
    (E : PolynomialRamifiedCodimensionOnePoint (F := F) (N := N)) :
    fixedMovingBoundarySupportIdeal B
      (inertiaGroupAt (PlanarBaseFunctionField F)
        (D.valuationAt E).valuationRing) ≤ E.1.asIdeal :=
  fixedMovingBoundarySupportIdeal_le_ramifiedPrime B E _ le_rfl

/--
The existing boundary-separation predicate is exactly the assertion that no
nontrivial fixed--moving support ideal lies in a height-one prime.
-/
theorem planarBoundarySeparation_iff_no_heightOne_fixedMovingSupport
    (B : BoundaryIdealData D) :
    B.PlanarBoundarySeparation ↔
      ∀ (C : Subgroup (NormalizationGaloisGroup D)), C ≠ ⊥ →
        ∀ p : PrimeSpectrum (GaloisNormalizationRing (F := F) (N := N)),
          p.asIdeal.primeHeight = 1 →
            ¬ fixedMovingBoundarySupportIdeal B C ≤ p.asIdeal := by
  constructor
  · intro h C hC p hp hCombined
    obtain ⟨hFixed, hMoving⟩ :=
      (fixedMovingBoundarySupportIdeal_le_iff B C p.asIdeal).mp hCombined
    exact (h C hC p hp hFixed) hMoving
  · intro h C hC p hp hFixed hMoving
    exact h C hC p hp
      ((fixedMovingBoundarySupportIdeal_le_iff B C p.asIdeal).mpr
        ⟨hFixed, hMoving⟩)

/--
The abstract uniform-annihilator target specialized to fixed--moving
boundary principal parts.
-/
def HasUniformFixedMovingBoundaryAnnihilator
    (B : BoundaryIdealData D)
    (C : Subgroup (NormalizationGaloisGroup D)) : Prop :=
  HasUniformCombinedSupportAnnihilator
    (GaloisNormalizationRing (F := F) (N := N))
    (fixedLocusIdeal C) (movingBoundaryIdeal B.boundaryIdeal C)

end

end CollisionIdeals.Planar
