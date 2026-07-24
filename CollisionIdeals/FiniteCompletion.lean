import Mathlib.RingTheory.Unramified.Locus

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u

variable {B A : Type u}
variable [CommRing B] [CommRing A] [Algebra B A]

/--
The ramification locus of an affine model is the complement of its
formally unramified locus.

For a finite morphism in characteristic zero, this is the locus where
ramification is visible on the finite model.
-/
def ramificationLocus : Set (PrimeSpectrum A) :=
  (Algebra.unramifiedLocus B A)ᶜ

/-- The boundary complementary to the principal open `D(f)`. -/
def principalBoundary (f : A) : Set (PrimeSpectrum A) :=
  (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum A))ᶜ

/--
If the restriction of an affine model to `D(f)` is formally unramified,
then every ramified point of the original model lies in the boundary
complementary to `D(f)`.

This is the unconditional first half of the finite-completion bridge:
étaleness on the planar open hides any ramification in the deleted
boundary.  Excluding such hidden boundary ramification is a separate
planar statement.
-/
theorem ramificationLocus_subset_principalBoundary
    (f : A)
    [Algebra.FormallyUnramified B (Localization.Away f)] :
    ramificationLocus (B := B) (A := A) ⊆ principalBoundary f := by
  have hopen :
      (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum A)) ⊆
        Algebra.unramifiedLocus B A :=
    (Algebra.basicOpen_subset_unramifiedLocus_iff
      (R := B) (A := A)).2 inferInstance
  intro p hpRam hpOpen
  exact hpRam (hopen hpOpen)

end

end CollisionIdeals
