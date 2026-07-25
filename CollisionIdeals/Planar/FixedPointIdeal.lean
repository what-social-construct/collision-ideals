import CollisionIdeals.FiniteCorrespondence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open MvPolynomial

/--
The ideal cutting out the intersection of a plane automorphism's graph
with the diagonal.
-/
def planeAutomorphismFixedPointIdeal
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial) :
    Ideal PlanePolynomial :=
  Ideal.span
    (Set.range fun i : Fin 2 ↦ γ (X i) - X i)

/--
Over `ℂ`, the fixed-point ideal is proper exactly when the polynomial
automorphism has a fixed point.
-/
theorem planeAutomorphismFixedPointIdeal_ne_top_iff
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial) :
    planeAutomorphismFixedPointIdeal γ ≠ ⊤ ↔
      PlaneAutomorphismHasFixedPoint γ := by
  rw [PlaneAutomorphismHasFixedPoint]
  constructor
  · intro hproper
    have hne :
        MvPolynomial.zeroLocus ℂ
            (planeAutomorphismFixedPointIdeal γ) ≠ ∅ := by
      intro hempty
      apply hproper
      apply Ideal.radical_eq_top.mp
      rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
        (k := ℂ) (K := ℂ) (planeAutomorphismFixedPointIdeal γ),
        hempty, MvPolynomial.vanishingIdeal_empty]
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    refine ⟨x, ?_⟩
    funext i
    change MvPolynomial.eval x (γ (X i)) = x i
    have hdiff :
        MvPolynomial.aeval x (γ (X i) - X i) = 0 := by
      exact
        hx _
          (Ideal.subset_span (Set.mem_range_self i))
    have hdiff' :
        MvPolynomial.eval x (γ (X i) - X i) = 0 := by
      simpa only [MvPolynomial.coe_aeval_eq_eval] using hdiff
    simpa [map_sub, sub_eq_zero] using hdiff'
  · rintro ⟨x, hx⟩ htop
    have hz :
        x ∈ MvPolynomial.zeroLocus ℂ
          (planeAutomorphismFixedPointIdeal γ) := by
      rw [planeAutomorphismFixedPointIdeal,
        MvPolynomial.zeroLocus_span]
      rintro _ ⟨i, rfl⟩
      change MvPolynomial.aeval x (γ (X i) - X i) = 0
      rw [map_sub, MvPolynomial.aeval_X]
      change MvPolynomial.eval x (γ (X i)) - x i = 0
      have hxi := congrFun hx i
      change MvPolynomial.eval x (γ (X i)) = x i at hxi
      exact sub_eq_zero.mpr hxi
    have hone :
        (1 : PlanePolynomial) ∈
          planeAutomorphismFixedPointIdeal γ := by
      rw [htop]
      exact Set.mem_univ 1
    have hzero :
        MvPolynomial.aeval x (1 : PlanePolynomial) = 0 :=
      hz 1 hone
    exact
      one_ne_zero
        ((MvPolynomial.aeval x).map_one.symm.trans hzero)

/--
Equivalently, the automorphism graph avoids the diagonal exactly when its
fixed-point ideal is the unit ideal.
-/
theorem planeAutomorphismFixedPointIdeal_eq_top_iff
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial) :
    planeAutomorphismFixedPointIdeal γ = ⊤ ↔
      PlaneAutomorphismGraphAvoidsDiagonal γ := by
  rw [planeAutomorphismGraphAvoidsDiagonal_iff,
    ← planeAutomorphismFixedPointIdeal_ne_top_iff]
  tauto

end

end CollisionIdeals
