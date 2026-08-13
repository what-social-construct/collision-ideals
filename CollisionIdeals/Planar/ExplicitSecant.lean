import CollisionIdeals.Planar.Secant
import Mathlib.Algebra.Polynomial.Identities

/-!
# The explicit planar divided-difference secant

`Planar.Secant` proves that suitable two-coordinate secant coefficients
exist.  For the Galois-equivariant research construction, an opaque choice
of coefficients is not enough: this file defines the ordered telescoping
divided differences used in the manuscript coefficient by coefficient.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar.ExplicitSecant

open MvPolynomial

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- The canonical factor `(x^n - y^n) / (x - y)`. -/
def powDifferenceFactor
    {A : Type*} [CommRing A] (x y : A) (n : ℕ) : A :=
  (Polynomial.powSubPowFactor x y n).1

theorem powDifferenceFactor_spec
    {A : Type*} [CommRing A] (x y : A) (n : ℕ) :
    x ^ n - y ^ n = powDifferenceFactor x y n * (x - y) :=
  (Polynomial.powSubPowFactor x y n).2

theorem map_powDifferenceFactor
    {S : Type*} [CommRing S] (f : PairRing R (Fin 2) →+* S)
    (x y : PairRing R (Fin 2)) (n : ℕ) :
    f (powDifferenceFactor x y n) =
      powDifferenceFactor (f x) (f y) n := by
  induction n with
  | zero => simp [powDifferenceFactor, Polynomial.powSubPowFactor]
  | succ n ih =>
      rcases n with _ | n
      · simp [powDifferenceFactor, Polynomial.powSubPowFactor]
      · simp only [powDifferenceFactor, Polynomial.powSubPowFactor]
        rw [map_add, map_mul, map_pow]
        change
          f (powDifferenceFactor x y (n + 1)) * f x + f y ^ (n + 1) =
            powDifferenceFactor (f x) (f y) (n + 1) * f x + f y ^ (n + 1)
        rw [ih]

theorem diagonalEval_powDifferenceFactor
    (i : Fin 2) (n : ℕ) :
    diagonalEval
        (powDifferenceFactor
          (X (Sum.inl i) : PairRing R (Fin 2)) (X (Sum.inr i)) n) =
      powDifferenceFactor (X i : SourceRing R (Fin 2)) (X i) n := by
  change diagonalEval.toRingHom
      (powDifferenceFactor
        (X (Sum.inl i) : PairRing R (Fin 2)) (X (Sum.inr i)) n) = _
  rw [map_powDifferenceFactor]
  simp [diagonalEval]

theorem powDifferenceFactor_self
    {A : Type*} [CommRing A] (x : A) (n : ℕ) :
    powDifferenceFactor x x n = n • x ^ (n - 1) := by
  induction n with
  | zero => simp [powDifferenceFactor, Polynomial.powSubPowFactor]
  | succ n ih =>
      rcases n with _ | n
      · simp [powDifferenceFactor, Polynomial.powSubPowFactor]
      · simp only [powDifferenceFactor, Polynomial.powSubPowFactor]
        change
          powDifferenceFactor x x (n + 1) * x + x ^ (n + 1) =
            (n + 2) • x ^ (n + 1)
        rw [ih]
        simp only [Nat.add_sub_cancel, pow_succ]
        rw [add_nsmul, add_nsmul]
        ring

/-- One monomial's contribution to the first telescoping difference. -/
def firstCoefficient
    (v : Fin 2 →₀ ℕ) (r : R) : PairRing R (Fin 2) :=
  C r *
    powDifferenceFactor (X (Sum.inl 0)) (X (Sum.inr 0)) (v 0) *
    X (Sum.inl 1) ^ (v 1)

/-- One monomial's contribution to the second telescoping difference. -/
def secondCoefficient
    (v : Fin 2 →₀ ℕ) (r : R) : PairRing R (Fin 2) :=
  C r * X (Sum.inr 0) ^ (v 0) *
    powDifferenceFactor (X (Sum.inl 1)) (X (Sum.inr 1)) (v 1)

/-- The explicit first telescoping divided difference. -/
def first (p : SourceRing R (Fin 2)) : PairRing R (Fin 2) :=
  p.sum firstCoefficient

/-- The explicit second telescoping divided difference. -/
def second (p : SourceRing R (Fin 2)) : PairRing R (Fin 2) :=
  p.sum secondCoefficient

theorem first_add (p q : SourceRing R (Fin 2)) :
    first (p + q) = first p + first q := by
  classical
  apply Finsupp.sum_add_index
  · intro v hv
    simp [firstCoefficient]
  · intro v hv r s
    simp [firstCoefficient, add_mul]

theorem second_add (p q : SourceRing R (Fin 2)) :
    second (p + q) = second p + second q := by
  classical
  apply Finsupp.sum_add_index
  · intro v hv
    simp [secondCoefficient]
  · intro v hv r s
    simp [secondCoefficient, add_mul]

theorem monomial_fin_two
    (v : Fin 2 →₀ ℕ) (r : R) :
    monomial v r = C r * X 0 ^ (v 0) * X 1 ^ (v 1) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_two]
  ring

theorem equation_monomial
    (v : Fin 2 →₀ ℕ) (r : R) :
    leftRename (monomial v r) - rightRename (monomial v r) =
      first (monomial v r) * diagonalGenerator (R := R) 0 +
        second (monomial v r) * diagonalGenerator (R := R) 1 := by
  rw [show first (monomial v r) = firstCoefficient v r by
        rw [first, sum_monomial_eq]
        simp [firstCoefficient],
    show second (monomial v r) = secondCoefficient v r by
        rw [second, sum_monomial_eq]
        simp [secondCoefficient],
    monomial_fin_two]
  simp only [map_mul, map_pow, leftRename_C, rightRename_C,
    leftRename_X, rightRename_X]
  have hx :=
    powDifferenceFactor_spec
      (A := PairRing R (Fin 2)) (X (Sum.inl 0)) (X (Sum.inr 0)) (v 0)
  have hy :=
    powDifferenceFactor_spec
      (A := PairRing R (Fin 2)) (X (Sum.inl 1)) (X (Sum.inr 1)) (v 1)
  simp only [firstCoefficient, secondCoefficient, diagonalGenerator]
  calc
    (C r : PairRing R (Fin 2)) * X (Sum.inl 0) ^ v 0 * X (Sum.inl 1) ^ v 1 -
          C r * X (Sum.inr 0) ^ v 0 * X (Sum.inr 1) ^ v 1 =
        C r * (X (Sum.inl 0) ^ v 0 - X (Sum.inr 0) ^ v 0) *
            X (Sum.inl 1) ^ v 1 +
          C r * X (Sum.inr 0) ^ v 0 *
            (X (Sum.inl 1) ^ v 1 - X (Sum.inr 1) ^ v 1) := by ring
    _ = _ := by rw [hx, hy]; ring

theorem equation (p : SourceRing R (Fin 2)) :
    leftRename p - rightRename p =
      first p * diagonalGenerator (R := R) 0 +
        second p * diagonalGenerator (R := R) 1 := by
  induction p using MvPolynomial.induction_on' with
  | monomial v r => exact equation_monomial v r
  | add p q hp hq =>
      rw [map_add, map_add, first_add, second_add]
      calc
        leftRename p + leftRename q - (rightRename p + rightRename q) =
            (leftRename p - rightRename p) +
              (leftRename q - rightRename q) := by ring
        _ = _ := by rw [hp, hq]; ring

theorem pderiv_zero_monomial_fin_two
    (v : Fin 2 →₀ ℕ) (r : R) :
    pderiv 0 (monomial v r) =
      C r * (v 0 • X 0 ^ (v 0 - 1)) * X 1 ^ (v 1) := by
  rw [pderiv_monomial, monomial_fin_two]
  simp only [Fin.isValue, map_mul]
  simp
  ring

theorem pderiv_one_monomial_fin_two
    (v : Fin 2 →₀ ℕ) (r : R) :
    pderiv 1 (monomial v r) =
      C r * X 0 ^ (v 0) * (v 1 • X 1 ^ (v 1 - 1)) := by
  rw [pderiv_monomial, monomial_fin_two]
  simp only [Fin.isValue, map_mul]
  simp
  ring

theorem diagonal_first_monomial
    (v : Fin 2 →₀ ℕ) (r : R) :
    diagonalEval (first (monomial v r)) = pderiv 0 (monomial v r) := by
  rw [show first (monomial v r) = firstCoefficient v r by
        rw [first, sum_monomial_eq]
        simp [firstCoefficient],
    firstCoefficient, map_mul, map_mul,
    diagonalEval_powDifferenceFactor, powDifferenceFactor_self, map_pow,
    pderiv_zero_monomial_fin_two]
  simp [diagonalEval]

theorem diagonal_second_monomial
    (v : Fin 2 →₀ ℕ) (r : R) :
    diagonalEval (second (monomial v r)) = pderiv 1 (monomial v r) := by
  rw [show second (monomial v r) = secondCoefficient v r by
        rw [second, sum_monomial_eq]
        simp [secondCoefficient],
    secondCoefficient, map_mul, map_mul, map_pow,
    diagonalEval_powDifferenceFactor,
    powDifferenceFactor_self, pderiv_one_monomial_fin_two]
  simp [diagonalEval]

theorem diagonal_first (p : SourceRing R (Fin 2)) :
    diagonalEval (first p) = pderiv 0 p := by
  induction p using MvPolynomial.induction_on' with
  | monomial v r => exact diagonal_first_monomial v r
  | add p q hp hq =>
      simp only [first_add, map_add, hp, hq]

theorem diagonal_second (p : SourceRing R (Fin 2)) :
    diagonalEval (second p) = pderiv 1 p := by
  induction p using MvPolynomial.induction_on' with
  | monomial v r => exact diagonal_second_monomial v r
  | add p q hp hq =>
      simp only [second_add, map_add, hp, hq]

/-- Explicit telescoping secant data, with no `Classical.choice`. -/
def data (p : SourceRing R (Fin 2)) : PlanarSecantData p where
  first := first p
  second := second p
  equation := equation p
  diagonal_first := diagonal_first p
  diagonal_second := diagonal_second p

/-- The determinant of the explicit telescoping secant matrix. -/
def determinant (F : Fin 2 → SourceRing R (Fin 2)) : PairRing R (Fin 2) :=
  secantDet
    (first (F 0)) (second (F 0))
    (first (F 1)) (second (F 1))

theorem diagonalEval_determinant
    (F : Fin 2 → SourceRing R (Fin 2)) :
    diagonalEval (determinant F) =
      pderiv 0 (F 0) * pderiv 1 (F 1) -
        pderiv 1 (F 0) * pderiv 0 (F 1) := by
  simp [determinant, secantDet, diagonal_first, diagonal_second]

end


end CollisionIdeals.Planar.ExplicitSecant
