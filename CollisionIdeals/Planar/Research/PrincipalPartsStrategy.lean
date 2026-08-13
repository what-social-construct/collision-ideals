import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Trace.Defs

/-!
# Trace-integral bounded-stage comparison

This file contains the generic trace-integral and transporter objects for the
prospective principal-parts strategy.  They are not needed to state or prove
the stable planar equivalence spine.  The intended missing input is a
Keller-specific nonzero multiplier placing the relevant boundary classes in
one bounded trace-dual stage.

Finite flatness alone does not provide a comparison from the whole
principal-parts module to a finite trace-dual quotient: locally at a hidden
divisor the former is `Frac(R) / R`, with unbounded pole order, whereas the
codifferent supplies only one bounded pole stage.
-/

set_option autoImplicit false

namespace CollisionIdeals.Planar

noncomputable section

universe u
universe v

variable (R : Type u) [CommRing R]

/--
The trace-integral dual submodule inside a generic field.  The intended
application is `B = ℂ[P,Q]`, `K = Frac(B)`, and `T = A_N ⊆ N`.

Calling this submodule a finite trace-dual *lattice* and identifying it with
`Hom_B(T,B)` additionally require faithful embeddings, a generic-fiber
identification `K ⊗[B] T ≃ₐ[K] N`, finite local freeness of `T / B`, and
generic separability.  Those geometric hypotheses and conclusions are
deliberately separate from this definition.
-/
def TraceIntegralSubmodule
    (B K T N : Type*)
    [CommRing B] [Field K] [CommRing T] [Field N]
    [Algebra B K] [Algebra B T] [Algebra B N] [Algebra K N] [Algebra T N]
    [IsScalarTower B K N] [IsScalarTower B T N]
    [FiniteDimensional K N] : Submodule T N where
  carrier := {z : N | ∀ a : T,
    Algebra.trace K N (z * algebraMap T N a) ∈ Set.range (algebraMap B K)}
  zero_mem' := by
    intro a
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro x y hx hy a
    obtain ⟨bx, hbx⟩ := hx a
    obtain ⟨by_, hby⟩ := hy a
    refine ⟨bx + by_, ?_⟩
    simp [hbx, hby, add_mul]
  smul_mem' := by
    intro r z hz a
    simpa [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] using hz (r * a)

section BoundedStageComparison

variable (M : Type v) [AddCommGroup M] [Module R M]

/--
The multipliers which carry every relevant principal part into a prescribed
bounded stage.  In the intended application, `M` is a rational
principal-parts module, `relevant` is its ramification-supported submodule,
and `bounded` is the image of the trace-dual quotient.
-/
def boundedStageComparisonIdeal
    (bounded relevant : Submodule R M) : Ideal R :=
  bounded.colon relevant

theorem mem_boundedStageComparisonIdeal_iff
    {bounded relevant : Submodule R M} {s : R} :
    s ∈ boundedStageComparisonIdeal R M bounded relevant ↔
      ∀ x ∈ relevant, s • x ∈ bounded :=
  Submodule.mem_colon

end BoundedStageComparison

end

end CollisionIdeals.Planar
