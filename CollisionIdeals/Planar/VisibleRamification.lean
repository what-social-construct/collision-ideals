import CollisionIdeals.Planar.NormalizationDiagram
import Mathlib.NumberTheory.RamificationInertia.Unramified

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace CollisionIdeals.Planar

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]

/--
Formal unramifiedness survives passage from a ring map to the induced map
between local rings at a prime.

This is the local ring adapter needed below to read scheme-theoretic
étaleness as `Algebra.IsUnramifiedAt`.
-/
lemma ringHom_formallyUnramified_localRingHom
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FormallyUnramified)
    (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyUnramified := by
  algebraize [f, Localization.localRingHom (J.comap f) J f rfl]
  haveI : Algebra.FormallyUnramified R S := hf
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime J) := inferInstance
  haveI : IsScalarTower R
      (Localization.AtPrime (J.comap (algebraMap R S)))
      (Localization.AtPrime J) :=
    .of_algebraMap_eq fun x ↦
      (Localization.localRingHom_to_map _ _ _ rfl x).symm
  change Algebra.FormallyUnramified
    (Localization.AtPrime (J.comap f)) (Localization.AtPrime J)
  exact Algebra.FormallyUnramified.of_comp R
    (Localization.AtPrime (J.comap (algebraMap R S)))
    (Localization.AtPrime J)

/--
Let `j : U ⟶ X` be an open immersion between affine schemes.  If the
composite `U ⟶ X ⟶ Spec R` is formally unramified, then `X` is unramified
over `R` at every point represented by `U`.

The proof cancels the stalk isomorphism supplied by the open immersion and
then identifies affine stalk maps with maps of localizations.
-/
lemma isUnramifiedAt_of_openImmersion_comp_formallyUnramified
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R C]
    (j : Spec (.of A) ⟶ Spec (.of C)) [IsOpenImmersion j]
    [AlgebraicGeometry.FormallyUnramified
      (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)))]
    (x : Spec (.of A)) :
    Algebra.IsUnramifiedAt R (j.base x).asIdeal := by
  let q := j.base x
  let p := Spec.map (CommRingCat.ofHom (algebraMap R C))
  have hcomp :
      RingHom.FormallyUnramified ((j ≫ p).stalkMap x).hom :=
    HasRingHomProperty.stalkMap
      (P := @AlgebraicGeometry.FormallyUnramified)
      ringHom_formallyUnramified_localRingHom
      (inferInstance :
        AlgebraicGeometry.FormallyUnramified (j ≫ p)) x
  have hpstalk :
      RingHom.FormallyUnramified (p.stalkMap q).hom := by
    rw [Scheme.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.FormallyUnramified.respectsIso.cancel_right_isIso] at hcomp
    exact hcomp
  have hlocal :
      RingHom.FormallyUnramified
        (Localization.localRingHom
          (q.asIdeal.comap (algebraMap R C)) q.asIdeal
          (algebraMap R C) rfl) :=
    (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso
        (CommRingCat.ofHom (algebraMap R C)) q)).mp hpstalk
  have hbase :
      RingHom.FormallyUnramified
        (algebraMap R
          (Localization.AtPrime
            (q.asIdeal.comap (algebraMap R C)))) := by
    rw [RingHom.formallyUnramified_algebraMap]
    exact Algebra.FormallyUnramified.of_isLocalization
      (q.asIdeal.comap (algebraMap R C)).primeCompl
  have htotal :
      RingHom.FormallyUnramified
        ((Localization.localRingHom
          (q.asIdeal.comap (algebraMap R C)) q.asIdeal
          (algebraMap R C) rfl).comp
            (algebraMap R
              (Localization.AtPrime
                (q.asIdeal.comap (algebraMap R C))))) :=
    RingHom.FormallyUnramified.stableUnderComposition
      (algebraMap R
        (Localization.AtPrime
          (q.asIdeal.comap (algebraMap R C))))
      (Localization.localRingHom
        (q.asIdeal.comap (algebraMap R C)) q.asIdeal
        (algebraMap R C) rfl)
      hbase hlocal
  rw [show
      (Localization.localRingHom
        (q.asIdeal.comap (algebraMap R C)) q.asIdeal
        (algebraMap R C) rfl).comp
          (algebraMap R
            (Localization.AtPrime
              (q.asIdeal.comap (algebraMap R C)))) =
        algebraMap R (Localization.AtPrime q.asIdeal) by
      ext y
      exact Localization.localRingHom_to_map _ _ _ rfl y] at htotal
  change Algebra.FormallyUnramified R
    (Localization.AtPrime q.asIdeal)
  exact RingHom.formallyUnramified_algebraMap.mp htotal

namespace NormalizationDiagram

variable (D : NormalizationDiagram (F := F) (N := N))

/-- The actual prime of `X̄` realizing one double-coset sheet class. -/
def centerPrime
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) :
    Ideal (PlanarFiniteCompletionRing F) :=
  (D.centerAtClass E q).asIdeal

instance centerPrime_isPrime
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) :
    (D.centerPrime E q).IsPrime :=
  (D.centerAtClass E q).isPrime

/--
The geometric ramification index of the prime on `X̄` selected by a
double-coset class.
-/
noncomputable def geometricRamificationIndex
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E) : ℕ :=
  Ideal.ramificationIdx
    (R := planarImageAlgebra F)
    (S := PlanarFiniteCompletionRing F)
    ((algebraMap
      (planarImageAlgebra F)
      (PlanarFiniteCompletionRing F)) :
        planarImageAlgebra F →+* PlanarFiniteCompletionRing F)
    (Ideal.under
      (B := PlanarFiniteCompletionRing F)
      (planarImageAlgebra F) (D.centerPrime E q))
    (D.centerPrime E q)

/--
The exact valuation-theoretic realization still required after constructing
the double-coset centers.

It records that the selected centers are divisorial and that their
geometric ramification indices are the standard group indices

`[I_E : I_E ∩ gHg⁻¹]`.

Unlike the older visible-sheet predicate, it does not assume the
consequence of étaleness; that consequence is proved below.
-/
structure ConjugateRamificationRealization : Prop where
  center_ne_bot :
    ∀ E q, D.centerPrime E q ≠ ⊥
  inertiaIndex_eq_geometricRamificationIndex :
    ∀ E q,
      D.inertiaIndex E q =
        D.geometricRamificationIndex E q

/--
An actual conjugate center that remains in the affine-plane open sheet is
unramified over the base.  This is derived from the open immersion and the
étaleness of the original planar map.
-/
theorem centerPrime_isUnramifiedAt_of_visible
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hEtale : IsEtale (planarSourceToImageBase F))
    (hVisible : D.ConjugateCenterVisible E q) :
    Algebra.IsUnramifiedAt
      (A := PlanarFiniteCompletionRing F)
      (planarImageAlgebra F) (D.centerPrime E q) := by
  letI : IsOpenImmersion (planarSourceToFiniteCompletion F) :=
    D.cover.intermediateOpen
  letI : IsEtale (planarSourceToImageBase F) := hEtale
  haveI : AlgebraicGeometry.FormallyUnramified
      (planarSourceToFiniteCompletion F ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap
            (planarImageAlgebra F)
            (PlanarFiniteCompletionRing F)))) := by
    change AlgebraicGeometry.FormallyUnramified
      (planarSourceToFiniteCompletion F ≫
        planarFiniteCompletionToBase F)
    rw [planarSourceToFiniteCompletion_comp_toBase]
    infer_instance
  rcases hVisible with ⟨x, hx⟩
  change Algebra.IsUnramifiedAt
    (planarImageAlgebra F) (D.centerAtClass E q).asIdeal
  rw [← hx]
  exact
    isUnramifiedAt_of_openImmersion_comp_formallyUnramified
      (planarSourceToFiniteCompletion F) x

/--
At a visible conjugate center, scheme-theoretic étaleness forces the
geometric ramification index to be one.
-/
theorem geometricRamificationIndex_eq_one_of_visible
    (R : D.ConjugateRamificationRealization)
    (E : RamifiedCodimensionOnePoint (F := F) (N := N))
    (q : D.sheetClasses E)
    (hEtale : IsEtale (planarSourceToImageBase F))
    (hVisible : D.ConjugateCenterVisible E q) :
    D.geometricRamificationIndex E q = 1 := by
  letI : Module.Finite
      (planarImageAlgebra F) (PlanarFiniteCompletionRing F) :=
    D.cover.finiteIntermediateModel
  letI : IsNoetherianRing (planarImageAlgebra F) := by
    unfold planarImageAlgebra
    infer_instance
  letI : IsNoetherianRing (PlanarFiniteCompletionRing F) :=
    IsNoetherianRing.of_finite
      (planarImageAlgebra F) (PlanarFiniteCompletionRing F)
  letI : Algebra.IsUnramifiedAt
      (A := PlanarFiniteCompletionRing F)
      (planarImageAlgebra F) (D.centerPrime E q) :=
    D.centerPrime_isUnramifiedAt_of_visible E q hEtale hVisible
  exact
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R.center_ne_bot E q)

/--
The former pointwise visible-sheet input is now a theorem: the standard
valuation-index formula plus étaleness gives inertia index one at every
visible conjugate center.
-/
theorem visibleConjugateSheetInertia
    (R : D.ConjugateRamificationRealization) :
    D.VisibleConjugateSheetInertia := by
  intro E q hEtale hVisible
  rw [R.inertiaIndex_eq_geometricRamificationIndex]
  exact
    D.geometricRamificationIndex_eq_one_of_visible
      R E q hEtale hVisible

end NormalizationDiagram

end

end CollisionIdeals.Planar
