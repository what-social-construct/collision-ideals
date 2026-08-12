import Mathlib.RingTheory.Finiteness.Basic

/-!
# Unbounded principal parts are not finite

This file formalizes the nonfiniteness half of the proposed planar
principal-parts contradiction.  At a hidden ramification divisor, the local
module is expected to be `K / R` for a DVR `R`.  Every individual principal
part is killed by some power of a uniformizer, but no single power kills all
principal parts because their pole orders are unbounded.

The theorem below isolates exactly that module-theoretic mechanism.  It does
not depend on the geometric comparison identifying localized boundary local
cohomology with `K / R`.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Every element is killed by some power of `t`, with an exponent depending on it. -/
def IsLocallyPowerTorsion (t : R) : Prop :=
  ∀ x : M, ∃ n : ℕ, t ^ n • x = 0

/-- No single power of `t` kills the entire module. -/
def HasUnboundedPowerTorsion (t : R) : Prop :=
  ∀ n : ℕ, ∃ x : M, t ^ n • x ≠ 0

/--
A finite locally `t`-power-torsion module has a uniform annihilating power
of `t`.
-/
theorem exists_uniform_power_annihilator_of_finite
    {t : R} [Module.Finite R M]
    (hTorsion : IsLocallyPowerTorsion R M t) :
    ∃ N : ℕ, ∀ x : M, t ^ N • x = 0 := by
  rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
  choose exponent hexponent using fun x : M => hTorsion x
  let N : ℕ := S.sup exponent
  refine ⟨N, fun x => ?_⟩
  have hx : x ∈ Submodule.span R (S : Set M) := by
    rw [hS]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      have hle : exponent x ≤ N := by
        exact Finset.le_sup hx
      calc
        t ^ N • x = (t ^ (N - exponent x) * t ^ exponent x) • x := by
          rw [← pow_add, Nat.sub_add_cancel hle]
        _ = t ^ (N - exponent x) • (t ^ exponent x • x) := by
          rw [mul_smul]
        _ = 0 := by rw [hexponent x, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [smul_add, hx, hy]
  | smul a x _ hx => simp [smul_comm, hx]

/--
Locally power-torsion principal parts with unbounded pole order cannot form a
finite module.
-/
theorem not_moduleFinite_of_unboundedPowerTorsion
    {t : R}
    (hTorsion : IsLocallyPowerTorsion R M t)
    (hUnbounded : HasUnboundedPowerTorsion R M t) :
    ¬ Module.Finite R M := by
  intro hFinite
  letI : Module.Finite R M := hFinite
  obtain ⟨N, hN⟩ :=
    exists_uniform_power_annihilator_of_finite R M hTorsion
  obtain ⟨x, hx⟩ := hUnbounded N
  exact hx (hN x)

end

end CollisionIdeals.Planar
