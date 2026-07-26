import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false

namespace CollisionIdeals

universe u v w

open MvPolynomial

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable {κ : Type w}

/-- Two labelled copies of the source variables. -/
abbrev PairVars (ι : Type v) := Sum ι ι

/-- The polynomial ring on one copy of affine space. -/
abbrev SourceRing (R : Type u) (ι : Type v) [CommRing R] :=
  MvPolynomial ι R

/-- The polynomial ring on two copies of affine space. -/
abbrev PairRing (R : Type u) (ι : Type v) [CommRing R] :=
  MvPolynomial (PairVars ι) R

/-- Put a polynomial in the left copy of the source variables. -/
def leftRename : SourceRing R ι →ₐ[R] PairRing R ι :=
  MvPolynomial.rename Sum.inl

/-- Put a polynomial in the right copy of the source variables. -/
def rightRename : SourceRing R ι →ₐ[R] PairRing R ι :=
  MvPolynomial.rename Sum.inr

/-- A standard generator `xᵢ(left) - xᵢ(right)` of the diagonal ideal. -/
def diagonalGenerator (i : ι) : PairRing R ι :=
  (X (Sum.inl i : PairVars ι) : PairRing R ι) -
    (X (Sum.inr i : PairVars ι) : PairRing R ι)

/-- The diagonal ideal in the coordinate ring of two copies of affine space. -/
def diagonalIdeal : Ideal (PairRing R ι) :=
  Ideal.span (Set.range (diagonalGenerator (R := R) (ι := ι)))

/-- A collision equation attached to an output coordinate of `F`. -/
def relationGenerator (F : κ → SourceRing R ι) (j : κ) : PairRing R ι :=
  leftRename (R := R) (ι := ι) (F j) -
    rightRename (R := R) (ι := ι) (F j)

/-- The collision ideal `I_R(F)`. -/
def relationIdeal (F : κ → SourceRing R ι) : Ideal (PairRing R ι) :=
  Ideal.span (Set.range (relationGenerator F))

/--
The collision-ideal name used in the geometric formulation.

`relationIdeal` remains the implementation name; this abbreviation exposes
the paper notation without introducing a second ideal.
-/
abbrev collisionIdeal
    (F : κ → SourceRing R ι) : Ideal (PairRing R ι) :=
  relationIdeal F

/-- The coordinate ring of the self-fiber product cut out by `I_R(F)`. -/
abbrev CollisionRing (F : κ → SourceRing R ι) :=
  PairRing R ι ⧸ relationIdeal F

/--
The image of `I_Δ` in the collision ring.  This is the ideal-theoretic
obstruction to the collision relation being exactly the diagonal.
-/
def obstructionIdeal (F : κ → SourceRing R ι) : Ideal (CollisionRing F) :=
  (diagonalIdeal (R := R) (ι := ι)).map
    (Ideal.Quotient.mk (relationIdeal F))

@[simp]
theorem leftRename_C (r : R) :
    leftRename (ι := ι) (C r) = C r := by
  simp [leftRename]

@[simp]
theorem rightRename_C (r : R) :
    rightRename (ι := ι) (C r) = C r := by
  simp [rightRename]

@[simp]
theorem leftRename_X (i : ι) :
    leftRename (R := R) (X i) = X (Sum.inl i) := by
  simp [leftRename]

@[simp]
theorem rightRename_X (i : ι) :
    rightRename (R := R) (X i) = X (Sum.inr i) := by
  simp [rightRename]

@[simp]
theorem leftRename_add (p q : SourceRing R ι) :
    leftRename (p + q) = leftRename p + leftRename q := by
  exact map_add _ _ _

@[simp]
theorem rightRename_add (p q : SourceRing R ι) :
    rightRename (p + q) = rightRename p + rightRename q := by
  exact map_add _ _ _

@[simp]
theorem leftRename_mul (p q : SourceRing R ι) :
    leftRename (p * q) = leftRename p * leftRename q := by
  exact map_mul _ _ _

@[simp]
theorem rightRename_mul (p q : SourceRing R ι) :
    rightRename (p * q) = rightRename p * rightRename q := by
  exact map_mul _ _ _

theorem diagonalGenerator_mem (i : ι) :
    diagonalGenerator (R := R) i ∈
      diagonalIdeal (R := R) (ι := ι) := by
  exact Ideal.subset_span (Set.mem_range_self i)

/-- Every polynomial difference between the two copies vanishes modulo `I_Δ`. -/
theorem left_sub_right_mem_diagonal (p : SourceRing R ι) :
    leftRename (R := R) (ι := ι) p -
        rightRename (R := R) (ι := ι) p ∈
      diagonalIdeal (R := R) (ι := ι) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp
  | add p q hp hq =>
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (diagonalIdeal (R := R) (ι := ι)).add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul, map_mul, leftRename_X, rightRename_X]
      rw [show
        leftRename p * X (Sum.inl i) -
            rightRename p * X (Sum.inr i) =
          X (Sum.inl i) * (leftRename p - rightRename p) +
            rightRename p *
              (X (Sum.inl i) - X (Sum.inr i)) by
        ring]
      exact
        (diagonalIdeal (R := R) (ι := ι)).add_mem
          ((diagonalIdeal (R := R) (ι := ι)).mul_mem_left _ hp)
          ((diagonalIdeal (R := R) (ι := ι)).mul_mem_left _
            (diagonalGenerator_mem (R := R) i))

/-- The canonical inclusion `I_R(F) ⊆ I_Δ`. -/
theorem relationIdeal_le_diagonalIdeal (F : κ → SourceRing R ι) :
    relationIdeal F ≤ diagonalIdeal (R := R) (ι := ι) := by
  rw [relationIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact left_sub_right_mem_diagonal (F j)

/--
The diagonal quotient map induced by the canonical inclusion
`I_R(F) ≤ I_Δ`.

On representatives it sends `f + I_R(F)` to `f + I_Δ`.
-/
def collisionDiagonalMap
    (F : κ → SourceRing R ι) :
    CollisionRing F →+*
      PairRing R ι ⧸ diagonalIdeal (R := R) (ι := ι) :=
  Ideal.Quotient.lift
    (relationIdeal F)
    (Ideal.Quotient.mk (diagonalIdeal (R := R) (ι := ι)))
    (by
      intro f hf
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact relationIdeal_le_diagonalIdeal F hf)

/-- Paper notation `bar μ_F` for the collision-to-diagonal map. -/
abbrev barMu
    (F : κ → SourceRing R ι) :
    CollisionRing F →+*
      PairRing R ι ⧸ diagonalIdeal (R := R) (ι := ι) :=
  collisionDiagonalMap F

/-- The collision-to-diagonal map is the evident map on representatives. -/
@[simp]
theorem collisionDiagonalMap_mk
    (F : κ → SourceRing R ι)
    (f : PairRing R ι) :
    collisionDiagonalMap F
        (Ideal.Quotient.mk (relationIdeal F) f) =
      Ideal.Quotient.mk
        (diagonalIdeal (R := R) (ι := ι)) f := by
  rfl

/-- The diagonal quotient factors through the collision quotient. -/
theorem collisionDiagonalMap_comp_quotientMk
    (F : κ → SourceRing R ι) :
    (collisionDiagonalMap F).comp
        (Ideal.Quotient.mk (relationIdeal F)) =
      Ideal.Quotient.mk
        (diagonalIdeal (R := R) (ι := ι)) := by
  rfl

/-- The collision-to-diagonal map is surjective. -/
theorem collisionDiagonalMap_surjective
    (F : κ → SourceRing R ι) :
    Function.Surjective (collisionDiagonalMap F) := by
  intro f
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective f
  exact
    ⟨Ideal.Quotient.mk (relationIdeal F) g,
      collisionDiagonalMap_mk F g⟩

/--
The obstruction ideal is literally the kernel of the induced diagonal map:
`ker(S / I_R(F) → S / I_Δ) = I_Δ / I_R(F)`.
-/
theorem collisionDiagonalMap_ker
    (F : κ → SourceRing R ι) :
    RingHom.ker (collisionDiagonalMap F) =
      obstructionIdeal F := by
  rw [collisionDiagonalMap, Ideal.ker_quotient_lift, Ideal.mk_ker]
  rfl

/--
Substituting the two copies of `F` into any polynomial produces a difference
lying in `I_R(F)`.
-/
theorem bind_left_sub_right_mem_relation
    (F : κ → SourceRing R ι) (p : MvPolynomial κ R) :
    leftRename (MvPolynomial.bind₁ F p) -
        rightRename (MvPolynomial.bind₁ F p) ∈ relationIdeal F := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp
  | add p q hp hq =>
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (relationIdeal F).add_mem hp hq
  | mul_X p j hp =>
      rw [map_mul, MvPolynomial.bind₁_X_right, map_mul, map_mul]
      rw [show
        leftRename (MvPolynomial.bind₁ F p) * leftRename (F j) -
            rightRename (MvPolynomial.bind₁ F p) * rightRename (F j) =
          leftRename (MvPolynomial.bind₁ F p) *
              (leftRename (F j) - rightRename (F j)) +
            (leftRename (MvPolynomial.bind₁ F p) -
                rightRename (MvPolynomial.bind₁ F p)) *
              rightRename (F j) by
        ring]
      exact
        (relationIdeal F).add_mem
          ((relationIdeal F).mul_mem_left _
            (Ideal.subset_span (Set.mem_range_self j)))
          ((relationIdeal F).mul_mem_right _ hp)

/-- A polynomial left inverse `G ∘ F = id` for a map with output variables `κ`. -/
def HasPolynomialLeftInverse (F : κ → SourceRing R ι) : Prop :=
  ∃ G : ι → MvPolynomial κ R,
    ∀ i, MvPolynomial.bind₁ F (G i) = X i

/--
A polynomial self-map is an automorphism when substitution by its
coordinate polynomials is a bijection of the coordinate polynomial ring.
-/
def IsPolynomialAutomorphism
    (F : ι → SourceRing R ι) : Prop :=
  Function.Bijective (MvPolynomial.bind₁ F)

/-- A polynomial automorphism has a polynomial left inverse. -/
theorem IsPolynomialAutomorphism.hasPolynomialLeftInverse
    {F : ι → SourceRing R ι}
    (hF : IsPolynomialAutomorphism F) :
    HasPolynomialLeftInverse F := by
  choose G hG using fun i ↦ hF.2 (X i)
  exact ⟨G, hG⟩

/-- A polynomial left inverse forces the collision relation to be the diagonal. -/
theorem relationIdeal_eq_diagonalIdeal_of_hasPolynomialLeftInverse
    (F : κ → SourceRing R ι) (hF : HasPolynomialLeftInverse F) :
    relationIdeal F = diagonalIdeal (R := R) (ι := ι) := by
  apply le_antisymm (relationIdeal_le_diagonalIdeal F)
  rw [diagonalIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨G, hG⟩ := hF
  have hmem := bind_left_sub_right_mem_relation F (G i)
  simpa [diagonalGenerator, hG i] using hmem

/-- The obstruction quotient vanishes exactly when `I_R(F) = I_Δ`. -/
theorem obstructionIdeal_eq_bot_iff (F : κ → SourceRing R ι) :
    obstructionIdeal F = ⊥ ↔
      relationIdeal F = diagonalIdeal (R := R) (ι := ι) := by
  rw [obstructionIdeal, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  constructor
  · intro h
    exact le_antisymm (relationIdeal_le_diagonalIdeal F) h
  · intro h
    rw [h]

/--
The induced diagonal map has zero kernel exactly when the collision and
diagonal ideals agree.
-/
theorem collisionDiagonalMap_ker_eq_bot_iff
    (F : κ → SourceRing R ι) :
    RingHom.ker (collisionDiagonalMap F) = ⊥ ↔
      relationIdeal F =
        diagonalIdeal (R := R) (ι := ι) := by
  rw [collisionDiagonalMap_ker, obstructionIdeal_eq_bot_iff]

/--
Equivalently, the collision-to-diagonal quotient map is injective exactly
when `I_R(F) = I_Δ`.
-/
theorem collisionDiagonalMap_injective_iff
    (F : κ → SourceRing R ι) :
    Function.Injective (collisionDiagonalMap F) ↔
      relationIdeal F =
        diagonalIdeal (R := R) (ι := ι) := by
  rw [RingHom.injective_iff_ker_eq_bot,
    collisionDiagonalMap_ker_eq_bot_iff]

/-- Evaluate the coordinate polynomials of `F` at a point. -/
def pointMap (F : κ → SourceRing R ι) (a : ι → R) : κ → R :=
  fun j ↦ MvPolynomial.eval a (F j)

/-- Evaluate the pair ring at the ordered pair `(a,b)`. -/
def pairEval (a b : ι → R) : PairRing R ι →+* R :=
  MvPolynomial.eval (Sum.elim a b)

theorem relationIdeal_le_pairEval_ker
    (F : κ → SourceRing R ι) (a b : ι → R)
    (h : pointMap F a = pointMap F b) :
    relationIdeal F ≤ RingHom.ker (pairEval a b) := by
  rw [relationIdeal, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  change pairEval a b
    (leftRename (F j) - rightRename (F j)) = 0
  have hj := congrFun h j
  change MvPolynomial.eval a (F j) = MvPolynomial.eval b (F j) at hj
  simp [pairEval, leftRename, rightRename, MvPolynomial.eval_rename, hj]

/-- If `I_R(F) = I_Δ`, then equality of images implies equality of points. -/
theorem pointMap_injective_of_relationIdeal_eq_diagonalIdeal
    (F : κ → SourceRing R ι)
    (hIdeal : relationIdeal F = diagonalIdeal (R := R) (ι := ι)) :
    Function.Injective (pointMap F) := by
  intro a b hCollision
  funext i
  have hmem :
      diagonalGenerator (R := R) i ∈ relationIdeal F := by
    rw [hIdeal]
    exact diagonalGenerator_mem i
  have hzero :=
    relationIdeal_le_pairEval_ker F a b hCollision hmem
  rw [RingHom.mem_ker] at hzero
  have : a i - b i = 0 := by
    simpa [pairEval, diagonalGenerator] using hzero
  exact sub_eq_zero.mp this

end

end CollisionIdeals
