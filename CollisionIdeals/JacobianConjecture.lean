import CollisionIdeals.Planar

set_option autoImplicit false

namespace CollisionIdeals

open MvPolynomial

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/--
A polynomial self-map is an automorphism when substitution by its
coordinate polynomials is a bijection of the coordinate polynomial ring.
-/
def IsPolynomialAutomorphism
    (F : ι → SourceRing R ι) : Prop :=
  Function.Bijective (MvPolynomial.bind₁ F)

/-- A polynomial automorphism has a polynomial left inverse. -/
theorem IsPolynomialAutomorphism.hasPolynomialLeftInverse
    {F : ι → SourceRing R ι}
    (hF : IsPolynomialAutomorphism F) :
    HasPolynomialLeftInverse F := by
  choose G hG using fun i ↦ hF.2 (X i)
  exact ⟨G, hG⟩

/-- Every polynomial automorphism has vanishing collision obstruction. -/
theorem obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
    {F : ι → SourceRing R ι}
    (hF : IsPolynomialAutomorphism F) :
    obstructionIdeal F = ⊥ := by
  apply (obstructionIdeal_eq_bot_iff F).2
  exact
    relationIdeal_eq_diagonalIdeal_of_hasPolynomialLeftInverse
      F hF.hasPolynomialLeftInverse

/--
The explicit complex-plane automorphism statement: every polynomial
self-map of `𝔸²_ℂ` with constant nonzero Jacobian determinant is a
polynomial automorphism of `𝔸²_ℂ`.
-/
def PlanarJacobianConjecture : Prop :=
  ∀ F : Fin 2 → PlanePolynomial,
    IsPlanarKeller F →
      IsPolynomialAutomorphism F

/--
The classical Ax--Grothendieck automorphism principle used in the
reformulation: an injective polynomial self-map of the complex affine
plane is a polynomial automorphism.

It is an explicit hypothesis below, not a new axiom of this development.
-/
def PlanarAxGrothendieck : Prop :=
  ∀ F : Fin 2 → PlanePolynomial,
    Function.Injective (pointMap F) →
      IsPolynomialAutomorphism F

/--
Assuming the classical Ax--Grothendieck principle, the obstruction detects
polynomial automorphisms map by map.
-/
theorem planarPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
    (hAx : PlanarAxGrothendieck)
    (F : Fin 2 → PlanePolynomial) :
    IsPolynomialAutomorphism F ↔
      obstructionIdeal F = ⊥ := by
  constructor
  · exact obstructionIdeal_eq_bot_of_isPolynomialAutomorphism
  · intro hObstruction
    apply hAx F
    exact
      pointMap_injective_of_relationIdeal_eq_diagonalIdeal F
        ((obstructionIdeal_eq_bot_iff F).1 hObstruction)

/--
Modulo Ax--Grothendieck, a polynomial self-map of the complex affine plane
is a polynomial automorphism exactly when its collision-to-diagonal map is
injective.
-/
theorem planarPolynomialAutomorphism_iff_collisionDiagonalMap_injective
    (hAx : PlanarAxGrothendieck)
    (F : Fin 2 → PlanePolynomial) :
    IsPolynomialAutomorphism F ↔
      Function.Injective (collisionDiagonalMap F) := by
  rw [RingHom.injective_iff_ker_eq_bot, collisionDiagonalMap_ker]
  exact
    planarPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
      hAx F

/--
Modulo the classical Ax--Grothendieck theorem, the usual planar Jacobian
conjecture is exactly vanishing of `I_Δ / I_R` for every planar Keller map.
-/
theorem planarJacobianConjecture_iff_planarVanishing
    (hAx : PlanarAxGrothendieck) :
    PlanarJacobianConjecture ↔ PlanarVanishing := by
  constructor
  · intro hJC F hKeller
    exact
      (planarPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
        hAx F).1
        (hJC F hKeller)
  · intro hVanishing F hKeller
    exact
      (planarPolynomialAutomorphism_iff_obstructionIdeal_eq_bot
        hAx F).2
        (hVanishing F hKeller)

/--
Modulo Ax--Grothendieck, the explicit statement that every planar Keller
map is a polynomial automorphism is equivalent to kernel vanishing for the
canonical collision-to-diagonal map.
-/
theorem planarJacobianConjecture_iff_planarKernelVanishing
    (hAx : PlanarAxGrothendieck) :
    PlanarJacobianConjecture ↔ PlanarKernelVanishing :=
  (planarJacobianConjecture_iff_planarVanishing hAx).trans
    planarKernelVanishing_iff_planarVanishing.symm

end

end CollisionIdeals
