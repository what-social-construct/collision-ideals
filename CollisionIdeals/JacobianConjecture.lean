import CollisionIdeals.AutomorphismCriterion
import CollisionIdeals.CollisionDiagonal
import CollisionIdeals.Keller
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

/-- A polynomial self-map of complex affine `n`-space. -/
abbrev ComplexPolynomialSelfMap (n : ℕ) :=
  PolynomialSelfMap ℂ n

/--
Ax--Grothendieck in dimension `n`: an injective polynomial self-map of
complex affine `n`-space is a polynomial automorphism.
-/
def ComplexAxGrothendieck (n : ℕ) : Prop :=
  ∀ F : ComplexPolynomialSelfMap n,
    Function.Injective (pointMap F) →
      IsPolynomialAutomorphism F

/-- The Jacobian conjecture in complex dimension `n`. -/
def ComplexJacobianConjecture (n : ℕ) : Prop :=
  ∀ F : ComplexPolynomialSelfMap n,
    IsKeller F →
      IsPolynomialAutomorphism F

/-- Collision-obstruction vanishing for every complex Keller map in dimension `n`. -/
def ComplexKellerVanishing (n : ℕ) : Prop :=
  ∀ F : ComplexPolynomialSelfMap n,
    IsKeller F →
      obstructionIdeal F = ⊥

/-- A Keller map that is not a polynomial automorphism. -/
def IsComplexJacobianCounterexample
    {n : ℕ} (F : ComplexPolynomialSelfMap n) : Prop :=
  IsKeller F ∧ ¬ IsPolynomialAutomorphism F

/--
Assuming Ax--Grothendieck in dimension `n`, the obstruction detects
polynomial automorphisms map by map.
-/
theorem complexPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
    {n : ℕ}
    (hAx : ComplexAxGrothendieck n)
    (F : ComplexPolynomialSelfMap n) :
    IsPolynomialAutomorphism F ↔
      obstructionIdeal F = ⊥ := by
  constructor
  · exact obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
  · intro hObstruction
    apply hAx F
    exact
      pointMap_injective_of_collisionIdeal_eq_diagonalIdeal F
        ((obstructionIdeal_eq_bot_iff F).1 hObstruction)

/--
Modulo Ax--Grothendieck, the Jacobian conjecture in dimension `n` is
exactly collision-obstruction vanishing for every Keller map.
-/
theorem complexJacobianConjecture_iff_kellerVanishing
    {n : ℕ}
    (hAx : ComplexAxGrothendieck n) :
    ComplexJacobianConjecture n ↔
      ComplexKellerVanishing n := by
  constructor
  · intro hJC F hKeller
    exact
      (complexPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
        hAx F).1
        (hJC F hKeller)
  · intro hVanishing F hKeller
    exact
      (complexPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
        hAx F).2
        (hVanishing F hKeller)

/--
Modulo Ax--Grothendieck, every possible Jacobian-conjecture counterexample
is exactly a Keller map with nonzero collision obstruction.
-/
theorem isComplexJacobianCounterexample_iff
    {n : ℕ}
    (hAx : ComplexAxGrothendieck n)
    (F : ComplexPolynomialSelfMap n) :
    IsComplexJacobianCounterexample F ↔
      IsKeller F ∧ obstructionIdeal F ≠ ⊥ := by
  unfold IsComplexJacobianCounterexample
  rw [not_congr
    (complexPolynomialAutomorphism_iff_obstructionIdeal_eq_bot hAx F)]

end

end CollisionIdeals
