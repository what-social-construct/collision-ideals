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
A finite-order algebra endomorphism is automatically an algebra
automorphism.  This is the algebraic step that turns a finite collision
graph into a symmetry.
-/
def algEquivOfFiniteOrder
    (γ : SourceRing R ι →ₐ[R] SourceRing R ι)
    (hγ : IsOfFinOrder γ) :
    SourceRing R ι ≃ₐ[R] SourceRing R ι :=
  AlgEquiv.algHomUnitsEquiv R (SourceRing R ι) hγ.unit

@[simp]
theorem algEquivOfFiniteOrder_apply
    (γ : SourceRing R ι →ₐ[R] SourceRing R ι)
    (hγ : IsOfFinOrder γ)
    (p : SourceRing R ι) :
    algEquivOfFiniteOrder γ hγ p = γ p := by
  rfl

theorem algEquivOfFiniteOrder_isOfFinOrder
    (γ : SourceRing R ι →ₐ[R] SourceRing R ι)
    (hγ : IsOfFinOrder γ) :
    IsOfFinOrder (algEquivOfFiniteOrder γ hγ) := by
  apply
    (AlgEquiv.algHomUnitsEquiv R (SourceRing R ι)).toMonoidHom.isOfFinOrder
  apply Units.isOfFinOrder_val.mp
  simpa using hγ

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
Finite order alone upgrades the graph endomorphism to a polynomial
automorphism; no separate bijectivity hypothesis on the second projection
is needed.
-/
def collisionGraphAutomorphismOfFiniteOrder
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hfiniteOrder : IsOfFinOrder (collisionGraphEndomorphism c e₁)) :
    SourceRing R ι ≃ₐ[R] SourceRing R ι :=
  algEquivOfFiniteOrder (collisionGraphEndomorphism c e₁) hfiniteOrder

@[simp]
theorem collisionGraphAutomorphismOfFiniteOrder_apply
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hfiniteOrder : IsOfFinOrder (collisionGraphEndomorphism c e₁))
    (p : SourceRing R ι) :
    collisionGraphAutomorphismOfFiniteOrder c e₁ hfiniteOrder p =
      collisionGraphEndomorphism c e₁ p := by
  rfl

theorem collisionGraphAutomorphismOfFiniteOrder_fixes
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hleft : c.left = e₁.toAlgHom)
    (hfiniteOrder : IsOfFinOrder (collisionGraphEndomorphism c e₁))
    (j : κ) :
    collisionGraphAutomorphismOfFiniteOrder c e₁ hfiniteOrder (F j) =
      F j := by
  rw [collisionGraphAutomorphismOfFiniteOrder_apply]
  exact collisionGraphEndomorphism_fixes c e₁ hleft j

theorem collisionGraphAutomorphismOfFiniteOrder_isOfFinOrder
    (c : CollisionCocone F T)
    (e₁ : SourceRing R ι ≃ₐ[R] T)
    (hfiniteOrder : IsOfFinOrder (collisionGraphEndomorphism c e₁)) :
    IsOfFinOrder
      (collisionGraphAutomorphismOfFiniteOrder c e₁ hfiniteOrder) :=
  algEquivOfFiniteOrder_isOfFinOrder
    (collisionGraphEndomorphism c e₁) hfiniteOrder

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

/-- The polynomial self-map on points represented contravariantly by an automorphism. -/
def planeAutomorphismPointMap
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial)
    (a : Fin 2 → ℂ) :
    Fin 2 → ℂ :=
  pointMap (fun i ↦ γ (X i)) a

/-- A polynomial automorphism of the affine plane has a fixed point. -/
def PlaneAutomorphismHasFixedPoint
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial) : Prop :=
  ∃ a : Fin 2 → ℂ,
    planeAutomorphismPointMap γ a = a

/-- The graph of a plane automorphism is disjoint from the diagonal. -/
def PlaneAutomorphismGraphAvoidsDiagonal
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial) : Prop :=
  ∀ a : Fin 2 → ℂ, planeAutomorphismPointMap γ a ≠ a

theorem planeAutomorphismGraphAvoidsDiagonal_iff
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial) :
    PlaneAutomorphismGraphAvoidsDiagonal γ ↔
      ¬ PlaneAutomorphismHasFixedPoint γ := by
  simp only [PlaneAutomorphismGraphAvoidsDiagonal,
    PlaneAutomorphismHasFixedPoint, not_exists]

/--
Evaluation after a coordinate-ring automorphism equals evaluation at the
corresponding point of its geometric automorphism.
-/
theorem eval_planeAutomorphism
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial)
    (a : Fin 2 → ℂ)
    (p : PlanePolynomial) :
    MvPolynomial.eval a (γ p) =
      MvPolynomial.eval (planeAutomorphismPointMap γ a) p := by
  let left : PlanePolynomial →ₐ[ℂ] ℂ :=
    (MvPolynomial.aeval a).comp γ.toAlgHom
  let right : PlanePolynomial →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval (planeAutomorphismPointMap γ a)
  have h : left = right := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [left, right, AlgHom.comp_apply, MvPolynomial.aeval_X]
    change
      MvPolynomial.aeval a (γ (X i)) =
        MvPolynomial.eval a (γ (X i))
    exact
      RingHom.congr_fun
        (MvPolynomial.coe_aeval_eq_eval a) (γ (X i))
  exact AlgHom.congr_fun h p

/--
If a plane automorphism fixes the coordinates of `F`, its graph consists
of collision pairs for `F`.
-/
theorem pointMap_planeAutomorphismPointMap_eq
    {F : Fin 2 → PlanePolynomial}
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial)
    (hfix : ∀ i, γ (F i) = F i)
    (a : Fin 2 → ℂ) :
    pointMap F (planeAutomorphismPointMap γ a) =
      pointMap F a := by
  funext i
  change
    MvPolynomial.eval (planeAutomorphismPointMap γ a) (F i) =
      MvPolynomial.eval a (F i)
  rw [← eval_planeAutomorphism γ a (F i), hfix i]

theorem relationIdeal_le_planeAutomorphismGraph_pairEval_ker
    {F : Fin 2 → PlanePolynomial}
    (γ : PlanePolynomial ≃ₐ[ℂ] PlanePolynomial)
    (hfix : ∀ i, γ (F i) = F i)
    (a : Fin 2 → ℂ) :
    relationIdeal F ≤
      RingHom.ker
        (pairEval a (planeAutomorphismPointMap γ a)) := by
  apply relationIdeal_le_pairEval_ker
  exact (pointMap_planeAutomorphismPointMap_eq γ hfix a).symm

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
The more primitive finite-component bridge.  Trivializing the first
projection naturally produces an endomorphism; finite order then upgrades
it canonically to the automorphism used by the fixed-point argument.
-/
structure FiniteComponentEndomorphismBridge
    (M : PlanarCollisionComponentModel Fp) where
  endomorphism :
    ∀ S, M.IsOffDiagonal S → M.FirstProjectionFinite S →
      PlanePolynomial →ₐ[ℂ] PlanePolynomial
  fixes :
    ∀ S hS hfinite i,
      endomorphism S hS hfinite (Fp i) = Fp i
  finiteOrder :
    ∀ S hS hfinite,
      IsOfFinOrder (endomorphism S hS hfinite)
  offDiagonal_fixedPointFree :
    ∀ S hS hfinite,
      ¬ PlaneAutomorphismHasFixedPoint
        (algEquivOfFiniteOrder
          (endomorphism S hS hfinite)
          (finiteOrder S hS hfinite))

/--
Finite order is the complete algebraic passage from the endomorphism
bridge to the automorphism bridge.
-/
def FiniteComponentEndomorphismBridge.toAutomorphismBridge
    {M : PlanarCollisionComponentModel Fp}
    (B : FiniteComponentEndomorphismBridge M) :
    FiniteComponentAutomorphismBridge M where
  automorphism S hS hfinite :=
    algEquivOfFiniteOrder
      (B.endomorphism S hS hfinite)
      (B.finiteOrder S hS hfinite)
  fixes S hS hfinite i := by
    rw [algEquivOfFiniteOrder_apply]
    exact B.fixes S hS hfinite i
  finiteOrder S hS hfinite :=
    algEquivOfFiniteOrder_isOfFinOrder
      (B.endomorphism S hS hfinite)
      (B.finiteOrder S hS hfinite)
  offDiagonal_fixedPointFree S hS hfinite :=
    B.offDiagonal_fixedPointFree S hS hfinite

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
The finite correspondence argument may start directly from graph
endomorphisms: finite order supplies all required invertibility.
-/
theorem finiteCorrespondenceRigidity_of_endomorphismBridge
    (M : PlanarCollisionComponentModel Fp)
    (B : FiniteComponentEndomorphismBridge M)
    (hFixedPoint : FiniteOrderPlaneAutomorphismFixedPoint) :
    FiniteCorrespondenceRigidity M :=
  finiteCorrespondenceRigidity_of_automorphismBridge
    M B.toAutomorphismBridge hFixedPoint

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
