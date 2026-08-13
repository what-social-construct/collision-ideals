import CollisionIdeals.BoundaryPrincipalParts
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Trace.Defs

/-!
# Ramification-supported principal parts

This file contains the local-cohomology objects for the prospective
principal-parts strategy.  They are not needed to state or prove the stable
planar equivalence spine.  The intended missing input is a Keller-specific
uniform bound placing the relevant boundary classes in one bounded
codifferent stage; after the intended height-one localization, a uniform
different-power annihilator is its corresponding algebraic form.

Finite flatness alone does not provide a comparison from the whole
principal-parts module to a finite trace-dual quotient: locally at a hidden
divisor the former is `Frac(R) / R`, with unbounded pole order, whereas the
codifferent supplies only one bounded pole stage.
-/

set_option autoImplicit false

open CategoryTheory

namespace CollisionIdeals.Planar

noncomputable section

universe u
universe v

variable (R : Type u) [CommRing R]

/--
Degree-zero local cohomology selects the part of the boundary principal-parts
module supported on a second ideal, intended in applications to be the
different or ramification ideal.
-/
def RamificationSupportedBoundaryPrincipalParts
    (d J : Ideal R) : ModuleCat R :=
  (localCohomology d 0).obj (BoundaryPrincipalParts R J)

/-- First local cohomology supported directly on the sum of two ideals. -/
def CombinedSupportPrincipalParts (d J : Ideal R) : ModuleCat R :=
  (localCohomology (d + J) 1).obj (ModuleCat.of R R)

/-- A positive power of an ideal annihilates a supplied module. -/
def HasUniformIdealPowerAnnihilator
    (I : Ideal R) (M : ModuleCat R) : Prop :=
  ∃ n : ℕ, 0 < n ∧ I ^ n ≤ Module.annihilator R M

/--
The uniform-annihilator target for the combined-support local-cohomology
module.  After the intended height-one localization this is the algebraic
counterpart of a bounded-codifferent-stage theorem.  No global equivalence
with the ramification-supported iterated local cohomology is asserted here;
its derivation from planar Keller data remains open.
-/
def HasUniformCombinedSupportAnnihilator (d J : Ideal R) : Prop :=
  HasUniformIdealPowerAnnihilator R (d + J)
    (CombinedSupportPrincipalParts R d J)

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

/--
Multiplication gives the canonical comparison from relevant principal parts
to homomorphisms from the comparison ideal into the bounded stage.
-/
def boundedStageComparisonMap
    (bounded relevant : Submodule R M) :
    relevant →ₗ[R]
      (boundedStageComparisonIdeal R M bounded relevant →ₗ[R] bounded) where
  toFun x :=
    { toFun := fun s =>
        ⟨(s : R) • (x : M),
          (Submodule.mem_colon.mp s.property) x x.property⟩
      map_add' := by
        intro s t
        ext
        simp [add_smul]
      map_smul' := by
        intro r s
        ext
        simp [mul_smul] }
  map_add' := by
    intro x y
    ext s
    simp [smul_add]
  map_smul' := by
    intro r x
    ext s
    change (s : R) • (r • (x : M)) = r • ((s : R) • (x : M))
    exact smul_comm _ _ _

/--
If the comparison ideal contains a global unit, the canonical bounded-stage
comparison is injective.  The analogous statement after avoiding a
height-one prime requires a separate localization theorem (including the
finite-presentation/Hom compatibility); it is not asserted here.
-/
theorem boundedStageComparisonMap_injective_of_isUnit_mem
    {bounded relevant : Submodule R M} {s : R}
    (hs : s ∈ boundedStageComparisonIdeal R M bounded relevant)
    (hUnit : IsUnit s) :
    Function.Injective (boundedStageComparisonMap R M bounded relevant) := by
  intro x y hxy
  apply Subtype.ext
  apply hUnit.smul_left_cancel.mp
  exact congrArg Subtype.val
    (DFunLike.congr_fun hxy
      (⟨s, hs⟩ : boundedStageComparisonIdeal R M bounded relevant))

end BoundedStageComparison

end

end CollisionIdeals.Planar
