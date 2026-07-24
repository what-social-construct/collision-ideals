import Mathlib.RingTheory.Unramified.Finite

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open Algebra
open scoped TensorProduct

universe u

variable {B A : Type u}
variable [CommRing B] [CommRing A] [Algebra B A]

/-- The coordinate algebra of the affine self-fiber product. -/
abbrev SelfFiberProductAlgebra :=
  A ⊗[B] A

/-- Multiplication is dual to the diagonal map into the self-fiber product. -/
def diagonalMultiplication :
    SelfFiberProductAlgebra (B := B) (A := A) →ₐ[B] A :=
  TensorProduct.lmul' B

/--
A tensor separating the diagonal from the other sheets of the self-fiber
product.  It restricts to `1` on the diagonal and annihilates every
difference between the two tensor factors.
-/
def IsDiagonalSeparator
    (t : SelfFiberProductAlgebra (B := B) (A := A)) : Prop :=
  (∀ a : A, ((1 : A) ⊗ₜ[B] a - a ⊗ₜ[B] (1 : A)) * t = 0) ∧
    diagonalMultiplication (B := B) (A := A) t = 1

/-- The complementary projector onto the off-diagonal part. -/
def fiberOffDiagonalProjector
    (t : SelfFiberProductAlgebra (B := B) (A := A)) :
    SelfFiberProductAlgebra (B := B) (A := A) :=
  1 - t

theorem mul_diagonalSeparator_eq
    {t : SelfFiberProductAlgebra (B := B) (A := A)}
    (ht : IsDiagonalSeparator (B := B) (A := A) t)
    (x : SelfFiberProductAlgebra (B := B) (A := A)) :
    x * t =
      ((diagonalMultiplication (B := B) (A := A) x) ⊗ₜ[B] (1 : A)) * t := by
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [diagonalMultiplication]
  | tmul a b =>
      have hb := ht.1 b
      rw [sub_mul, sub_eq_zero] at hb
      rw [diagonalMultiplication, TensorProduct.lmul'_apply_tmul]
      calc
        (a ⊗ₜ[B] b) * t =
            ((a ⊗ₜ[B] (1 : A)) * ((1 : A) ⊗ₜ[B] b)) * t := by
              rw [TensorProduct.tmul_mul_tmul]
              simp
        _ = (a ⊗ₜ[B] (1 : A)) * (((1 : A) ⊗ₜ[B] b) * t) := by
              rw [mul_assoc]
        _ = (a ⊗ₜ[B] (1 : A)) * ((b ⊗ₜ[B] (1 : A)) * t) := by
              rw [hb]
        _ = (((a * b) ⊗ₜ[B] (1 : A)) * t) := by
              rw [← mul_assoc, TensorProduct.tmul_mul_tmul]
              simp
  | add x y hx hy =>
      rw [add_mul, map_add, TensorProduct.add_tmul, add_mul, hx, hy]

theorem diagonalSeparator_isIdempotent
    {t : SelfFiberProductAlgebra (B := B) (A := A)}
    (ht : IsDiagonalSeparator (B := B) (A := A) t) :
    IsIdempotentElem t := by
  rw [IsIdempotentElem, mul_diagonalSeparator_eq ht t, ht.2]
  change (1 : SelfFiberProductAlgebra (B := B) (A := A)) * t = t
  exact one_mul t

theorem fiberOffDiagonalProjector_isIdempotent
    {t : SelfFiberProductAlgebra (B := B) (A := A)}
    (ht : IsDiagonalSeparator (B := B) (A := A) t) :
    IsIdempotentElem
      (fiberOffDiagonalProjector (B := B) (A := A) t) := by
  exact (diagonalSeparator_isIdempotent ht).one_sub

theorem diagonalMultiplication_fiberOffDiagonalProjector
    {t : SelfFiberProductAlgebra (B := B) (A := A)}
    (ht : IsDiagonalSeparator (B := B) (A := A) t) :
    diagonalMultiplication (B := B) (A := A)
      (fiberOffDiagonalProjector (B := B) (A := A) t) = 0 := by
  rw [fiberOffDiagonalProjector, map_sub, map_one, ht.2, sub_self]

/--
The ideal defining the diagonal inside the self-fiber product is generated
by the off-diagonal projector.
-/
theorem diagonalMultiplication_ker_eq_span_offDiagonalProjector
    {t : SelfFiberProductAlgebra (B := B) (A := A)}
    (ht : IsDiagonalSeparator (B := B) (A := A) t) :
    RingHom.ker
        (diagonalMultiplication (B := B) (A := A)).toRingHom =
      Ideal.span
        {fiberOffDiagonalProjector (B := B) (A := A) t} := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_span_singleton']
    refine ⟨x, ?_⟩
    have hμ :
        diagonalMultiplication (B := B) (A := A) x = 0 := by
      exact hx
    rw [fiberOffDiagonalProjector, mul_sub, mul_one,
      mul_diagonalSeparator_eq ht x, hμ]
    simp
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change
      diagonalMultiplication (B := B) (A := A)
        (fiberOffDiagonalProjector (B := B) (A := A) t) = 0
    exact diagonalMultiplication_fiberOffDiagonalProjector ht

/--
For an essentially finite-type algebra, formal unramifiedness is exactly
the existence of a diagonal-separating tensor in its self-fiber product.
-/
theorem formallyUnramified_iff_exists_diagonalSeparator
    [Algebra.EssFiniteType B A] :
    Algebra.FormallyUnramified B A ↔
      ∃ t : SelfFiberProductAlgebra (B := B) (A := A),
        IsDiagonalSeparator (B := B) (A := A) t := by
  exact Algebra.FormallyUnramified.iff_exists_tensorProduct

end

end CollisionIdeals
