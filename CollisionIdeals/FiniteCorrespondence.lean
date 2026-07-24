import CollisionIdeals.Planar
import CollisionIdeals.UniversalProperty
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

namespace CollisionIdeals

universe u v w z

open MvPolynomial

noncomputable section

variable {R : Type u} [CommRing R]
variable {ι : Type v}
variable {κ : Type w}
variable {T : Type z} [CommRing T] [Algebra R T]
variable {F : κ → SourceRing R ι}

/-- An endomorphism fixes a polynomial map when it fixes every output coordinate. -/
def FixesPolynomialMap
    (γ : SourceRing R ι →ₐ[R] SourceRing R ι)
    (F : κ → SourceRing R ι) : Prop :=
  ∀ j, γ (F j) = F j

/-- The collision cocone defined by the graph of an endomorphism fixing `F`. -/
def graphCollisionCocone
    (F : κ → SourceRing R ι)
    (γ : SourceRing R ι →ₐ[R] SourceRing R ι)
    (hγ : FixesPolynomialMap γ F) :
    CollisionCocone F (SourceRing R ι) where
  left := AlgHom.id R (SourceRing R ι)
  right := γ
  agree := fun j ↦ (hγ j).symm

/--
After trivializing the first projection of a collision correspondence, the
second projection becomes an endomorphism of the source coordinate ring.
-/
def collisionGraphEndomorphism
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T) :
    SourceRing R ι →ₐ[R] SourceRing R ι :=
  e₁.symm.toAlgHom.comp c.right

/--
If the chosen equivalence is the first collision projection, the graph
endomorphism fixes every coordinate of `F`.
-/
theorem collisionGraphEndomorphism_fixes
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hleft : c.left = e₁.toAlgHom)
    (j : κ) :
    collisionGraphEndomorphism c e₁ (F j) = F j := by
  change e₁.symm (c.right (F j)) = F j
  rw [← c.agree j, hleft]
  exact e₁.symm_apply_apply (F j)

/--
The original second projection is recovered from the graph endomorphism
and the trivialization of the first projection.
-/
theorem collisionGraphEndomorphism_factor_right
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T) :
    e₁.toAlgHom.comp (collisionGraphEndomorphism c e₁) =
      c.right := by
  apply AlgHom.ext
  intro p
  simp [collisionGraphEndomorphism]

/--
When the second projection is also bijective, the graph endomorphism is a
polynomial automorphism.
-/
def collisionGraphAutomorphism
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hright : Function.Bijective c.right) :
    SourceRing R ι ≃ₐ[R] SourceRing R ι :=
  AlgEquiv.ofBijective
    (collisionGraphEndomorphism c e₁)
    (e₁.symm.bijective.comp hright)

@[simp]
theorem collisionGraphAutomorphism_apply
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hright : Function.Bijective c.right)
    (p : SourceRing R ι) :
    collisionGraphAutomorphism c e₁ hright p =
      collisionGraphEndomorphism c e₁ p := by
  rfl

theorem collisionGraphAutomorphism_fixes
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hleft : c.left = e₁.toAlgHom)
    (hright : Function.Bijective c.right)
    (j : κ) :
    collisionGraphAutomorphism c e₁ hright (F j) = F j := by
  exact collisionGraphEndomorphism_fixes c e₁ hleft j

@[simp]
theorem collisionGraphEndomorphism_graphCollisionCocone
    (F : κ → SourceRing R ι)
    (γ : SourceRing R ι →ₐ[R] SourceRing R ι)
    (hγ : FixesPolynomialMap γ F) :
    collisionGraphEndomorphism
        (graphCollisionCocone F γ hγ)
        (AlgEquiv.refl : SourceRing R ι ≃ₐ[R] SourceRing R ι) =
      γ := by
  rfl

section Plane

/-- A polynomial automorphism of the affine plane has a fixed point. -/
def PlaneAutomorphismHasFixedPoint
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial) : Prop :=
  ∃ a : Fin 2 → ℂ,
    pointMap (fun i ↦ γ (X i)) a = a

/--
The classical affine-plane fixed-point input used by the finite
correspondence argument.
-/
def FiniteOrderPlaneAutomorphismFixedPoint : Prop :=
  ∀ γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial,
    IsOfFinOrder γ →
      PlaneAutomorphismHasFixedPoint γ

variable {Fp : Fin 2 → PlanePolynomial}

/--
The geometric bridge attaching a deck automorphism to every hypothetical
finite off-diagonal collision component.
-/
structure FiniteComponentAutomorphismBridge
    (M : PlanarCollisionComponentModel Fp) where
  automorphism :
    ∀ S, M.IsOffDiagonal S → M.FirstProjectionFinite S →
      PlanePolynomial ≃ₐ[ℂ] PlanePolynomial
  fixes :
    ∀ S hS hfinite i,
      automorphism S hS hfinite (Fp i) = Fp i
  finiteOrder :
    ∀ S hS hfinite,
      IsOfFinOrder (automorphism S hS hfinite)
  offDiagonal_fixedPointFree :
    ∀ S hS hfinite,
      ¬ PlaneAutomorphismHasFixedPoint
        (automorphism S hS hfinite)

/--
Finite-order fixed-point rigidity of the affine plane excludes every
finite off-diagonal collision component.
-/
theorem finiteCorrespondenceRigidity_of_automorphismBridge
    (M : PlanarCollisionComponentModel Fp)
    (B : FiniteComponentAutomorphismBridge M)
    (hFixedPoint : FiniteOrderPlaneAutomorphismFixedPoint) :
    FiniteCorrespondenceRigidity M := by
  intro S hS hfinite
  exact
    B.offDiagonal_fixedPointFree S hS hfinite
      (hFixedPoint
        (B.automorphism S hS hfinite)
        (B.finiteOrder S hS hfinite))

/--
The complete componentwise planar implication with the finite
correspondence side supplied by graph automorphisms.
-/
theorem planarVanishing_of_automorphismBridge_and_boundaryFiniteness
    (model :
      ∀ F : Fin 2 → PlanePolynomial,
        PlanarCollisionComponentModel F)
    (bridge :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          FiniteComponentAutomorphismBridge (model F))
    (hFixedPoint : FiniteOrderPlaneAutomorphismFixedPoint)
    (hFinite :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          PlanarBoundaryFiniteness (model F)) :
    PlanarVanishing := by
  apply planarVanishing_of_finite_and_nonfinite model
  · intro F hF
    exact
      finiteCorrespondenceRigidity_of_automorphismBridge
        (model F) (bridge F hF) hFixedPoint
  · exact hFinite

end Plane

end

end CollisionIdeals
