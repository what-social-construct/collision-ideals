import CollisionIdeals.Basic

set_option autoImplicit false

namespace CollisionIdeals

universe u v w

open MvPolynomial

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable {κ : Type w}

/-- Collapse the two labelled copies of the source variables to one copy. -/
def diagonalEval : PairRing R ι →ₐ[R] SourceRing R ι :=
  MvPolynomial.rename (Sum.elim id id)

@[simp]
theorem diagonalEval_leftRename (p : SourceRing R ι) :
    diagonalEval (R := R) (ι := ι) (leftRename p) = p := by
  simp [diagonalEval, leftRename, MvPolynomial.rename_rename]

@[simp]
theorem diagonalEval_rightRename (p : SourceRing R ι) :
    diagonalEval (R := R) (ι := ι) (rightRename p) = p := by
  simp [diagonalEval, rightRename, MvPolynomial.rename_rename]

@[simp]
theorem diagonalEval_diagonalGenerator (i : ι) :
    diagonalEval (R := R) (diagonalGenerator (R := R) i) = 0 := by
  simp [diagonalEval, diagonalGenerator]

/--
Every polynomial in the two copies differs from the left copy of its
diagonal restriction by an element of the diagonal ideal.
-/
theorem sub_leftRename_diagonalEval_mem (p : PairRing R ι) :
    p - leftRename (diagonalEval (R := R) (ι := ι) p) ∈
      diagonalIdeal (R := R) (ι := ι) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp
  | add p q hp hq =>
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (diagonalIdeal (R := R) (ι := ι)).add_mem hp hq
  | mul_X p i hp =>
      cases i with
      | inl i =>
          rw [map_mul, map_mul, diagonalEval, rename_X, leftRename_X]
          simp only [Sum.elim_inl]
          change
            p * X (Sum.inl i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) ∈
              diagonalIdeal (R := R) (ι := ι)
          rw [show
            p * X (Sum.inl i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) =
              X (Sum.inl i) *
                (p - leftRename (diagonalEval (R := R) (ι := ι) p)) by
            ring]
          exact
            (diagonalIdeal (R := R) (ι := ι)).mul_mem_left _ hp
      | inr i =>
          rw [map_mul, map_mul, diagonalEval, rename_X, leftRename_X]
          simp only [Sum.elim_inr]
          change
            p * X (Sum.inr i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) ∈
              diagonalIdeal (R := R) (ι := ι)
          rw [show
            p * X (Sum.inr i) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  X (Sum.inl i) =
              X (Sum.inr i) *
                  (p - leftRename (diagonalEval (R := R) (ι := ι) p)) -
                leftRename (diagonalEval (R := R) (ι := ι) p) *
                  diagonalGenerator (R := R) i by
            simp [diagonalGenerator]
            ring]
          exact
            (diagonalIdeal (R := R) (ι := ι)).sub_mem
              ((diagonalIdeal (R := R) (ι := ι)).mul_mem_left _ hp)
              ((diagonalIdeal (R := R) (ι := ι)).mul_mem_left _
                (diagonalGenerator_mem (R := R) i))

/-- The diagonal ideal is exactly the kernel of diagonal evaluation. -/
theorem diagonalEval_ker :
    RingHom.ker (diagonalEval (R := R) (ι := ι)).toRingHom =
      diagonalIdeal (R := R) (ι := ι) := by
  apply le_antisymm
  · intro p hp
    have hsub := sub_leftRename_diagonalEval_mem (R := R) (ι := ι) p
    change diagonalEval (R := R) (ι := ι) p = 0 at hp
    rw [hp, map_zero] at hsub
    simpa using hsub
  · rw [diagonalIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change diagonalEval (R := R) (ι := ι)
      (diagonalGenerator (R := R) i) = 0
    exact diagonalEval_diagonalGenerator (R := R) i

/-- The collision equations vanish under diagonal evaluation. -/
theorem relationIdeal_le_diagonalEval_ker
    (F : κ → SourceRing R ι) :
    relationIdeal F ≤
      RingHom.ker (diagonalEval (R := R) (ι := ι)).toRingHom := by
  rw [diagonalEval_ker]
  exact relationIdeal_le_diagonalIdeal F

/--
The morphism on coordinate rings dual to the diagonal
`X → X ×_Y X`.
-/
def collisionDiagonal (F : κ → SourceRing R ι) :
    CollisionRing F →ₐ[R] SourceRing R ι :=
  Ideal.Quotient.liftₐ
    (relationIdeal F)
    (diagonalEval (R := R) (ι := ι))
    (relationIdeal_le_diagonalEval_ker F)

@[simp]
theorem collisionDiagonal_mk
    (F : κ → SourceRing R ι) (p : PairRing R ι) :
    collisionDiagonal F (Ideal.Quotient.mk (relationIdeal F) p) =
      diagonalEval (R := R) (ι := ι) p := by
  rfl

/--
The concrete obstruction ideal is precisely the ideal defining the diagonal
inside the collision fiber product.
-/
theorem collisionDiagonal_ker (F : κ → SourceRing R ι) :
    RingHom.ker (collisionDiagonal F).toRingHom = obstructionIdeal F := by
  change
    RingHom.ker
        (Ideal.Quotient.lift
          (relationIdeal F)
          (diagonalEval (R := R) (ι := ι)).toRingHom
          (relationIdeal_le_diagonalEval_ker F)) =
      obstructionIdeal F
  rw [Ideal.ker_quotient_lift, diagonalEval_ker]
  rfl

end

end CollisionIdeals
