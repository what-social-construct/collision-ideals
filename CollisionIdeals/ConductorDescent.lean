import Mathlib.Algebra.Group.Idempotent
import Mathlib.RingTheory.Ideal.Quotient.Defs

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {C D : Type u}
variable [CommRing C] [CommRing D]

/--
The conductor of a ring map `f : C → D`, regarded as an ideal of `D`.
It is the largest ideal of `D` contained in the image of `f`.
-/
def extensionConductor (f : C →+* D) : Ideal D where
  carrier := {d | ∀ z : D, d * z ∈ Set.range f}
  zero_mem' := by
    intro z
    exact ⟨0, by simp⟩
  add_mem' := by
    intro d e hd he z
    obtain ⟨a, ha⟩ := hd z
    obtain ⟨b, hb⟩ := he z
    refine ⟨a + b, ?_⟩
    rw [map_add, ha, hb, add_mul]
  smul_mem' := by
    intro c d hd z
    simpa [mul_assoc, mul_left_comm, mul_comm] using hd (c * z)

/-- Every conductor element already belongs to the image of the smaller ring. -/
theorem extensionConductor_le_range
    (f : C →+* D) :
    (extensionConductor f : Set D) ⊆ Set.range f := by
  intro d hd
  simpa using hd 1

/--
An element of `D` descends to `C` exactly when its residue modulo the
conductor descends.  This is the algebraic form of descent across the
locus where normalization branches are glued.
-/
theorem mem_range_iff_quotient_conductor_mem_range
    (f : C →+* D) (q : D) :
    q ∈ Set.range f ↔
      Ideal.Quotient.mk (extensionConductor f) q ∈
        Set.range
          ((Ideal.Quotient.mk (extensionConductor f)).comp f) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    have hdiff : q - f c ∈ extensionConductor f := by
      apply
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem
          (I := extensionConductor f) q (f c)).mp
      simpa using hc.symm
    obtain ⟨d, hd⟩ := extensionConductor_le_range f hdiff
    refine ⟨d + c, ?_⟩
    rw [map_add, hd]
    exact sub_add_cancel q (f c)

/--
For an injective extension, a descended idempotent has an idempotent
preimage.  Thus descent preserves the corresponding clopen decomposition.
-/
theorem exists_idempotent_preimage
    (f : C →+* D) (hf : Function.Injective f)
    (q : D) (hq : IsIdempotentElem q)
    (hdesc : q ∈ Set.range f) :
    ∃ e : C, IsIdempotentElem e ∧ f e = q := by
  obtain ⟨e, he⟩ := hdesc
  refine ⟨e, ?_, he⟩
  rw [IsIdempotentElem]
  apply hf
  rw [map_mul, he]
  exact hq

/--
For an injective normalization map, an idempotent descends exactly when
its residue modulo the conductor descends.

This packages the conductor test for extending the diagonal/off-diagonal
component labels from a normalization back to the completed collision
algebra.
-/
theorem exists_idempotent_preimage_iff_quotient_conductor
    (f : C →+* D) (hf : Function.Injective f)
    (q : D) (hq : IsIdempotentElem q) :
    (∃ e : C, IsIdempotentElem e ∧ f e = q) ↔
      Ideal.Quotient.mk (extensionConductor f) q ∈
        Set.range
          ((Ideal.Quotient.mk (extensionConductor f)).comp f) := by
  constructor
  · rintro ⟨e, _, rfl⟩
    exact ⟨e, rfl⟩
  · intro hmod
    exact
      exists_idempotent_preimage f hf q hq
        ((mem_range_iff_quotient_conductor_mem_range f q).2 hmod)

end

end CollisionIdeals
