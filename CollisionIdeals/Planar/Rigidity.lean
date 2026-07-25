import CollisionIdeals.GaloisSheets
import CollisionIdeals.Planar.Components

set_option autoImplicit false

namespace CollisionIdeals

universe u

noncomputable section

section GaloisBridge

variable {G : Type u} [Group G]
variable {F : Fin 2 → PlanePolynomial}

/--
The global finite-normalization data for the normal closure of a planar map.

`visibleSheets B` records precisely the sheets of `G/H` whose codimension-one
centers over `B` remain in the affine-plane open model.  The field
`etale_visible` says that inertia fixes each such sheet.

The final two fields keep the standard global bridge in two explicit steps:
a nonzero collision obstruction makes the actual normal closure nontrivial,
and purity together with the absence of nontrivial finite étale covers of
the affine plane then produces nontrivial divisorial inertia.  This is
deliberately global; a single nonfinite collision component need not itself
carry ramification.
-/
structure PlanarGaloisInertiaModel
    (F : Fin 2 → PlanePolynomial) where
  finite_group : Finite G
  H : Subgroup G
  BranchDivisor : Type u
  inertiaGroup : BranchDivisor → Subgroup G
  visibleSheets : BranchDivisor → Set (GaloisSheets H)
  normalClosure_coreFree : H.normalCore = ⊥
  etale_visible :
    ∀ B, InertiaInvisibleOn (inertiaGroup B) H (visibleSheets B)
  obstruction_ne_bot_normalClosure_nontrivial :
    obstructionIdeal F ≠ ⊥ →
      (⊤ : Subgroup G) ≠ ⊥
  normalClosure_nontrivial_has_inertia :
    (⊤ : Subgroup G) ≠ ⊥ →
        ∃ B, inertiaGroup B ≠ ⊥

/--
The specifically planar rigidity assertion: the sheets that remain visible
in the affine-plane intermediate model detect each actual divisorial inertia
group of the normal closure.

This is the formal target corresponding to “a nontrivial Galois cover cannot
hide all of its inertia in the deleted boundary.”
-/
def PlanarHiddenInertiaRigidity
    (Z : PlanarGaloisInertiaModel F (G := G)) : Prop :=
  ∀ B,
    InertiaInvisibleOn
        (Z.inertiaGroup B) Z.H (Z.visibleSheets B) →
      Z.inertiaGroup B = ⊥

/-- Planar hidden-inertia rigidity kills every divisorial inertia group. -/
theorem inertiaGroup_eq_bot_of_planarHiddenInertiaRigidity
    (Z : PlanarGaloisInertiaModel F (G := G))
    (hRigidity : PlanarHiddenInertiaRigidity Z)
    (B : Z.BranchDivisor) :
    Z.inertiaGroup B = ⊥ := by
  exact hRigidity B (Z.etale_visible B)

/--
A visible set that detects every subgroup in particular detects each actual
inertia subgroup.
-/
theorem planarHiddenInertiaRigidity_of_visibleSheetsDetectInertia
    (Z : PlanarGaloisInertiaModel F (G := G))
    (hDetect :
      ∀ B, VisibleSheetsDetectInertia Z.H (Z.visibleSheets B)) :
    PlanarHiddenInertiaRigidity Z := by
  intro B hInvisible
  exact hDetect B (Z.inertiaGroup B) hInvisible

/--
If every sheet remains visible, core-freeness already gives hidden-inertia
rigidity.  The planar difficulty is to retain this detection property when
some sheets lie on the deleted boundary.
-/
theorem planarHiddenInertiaRigidity_of_allSheetsVisible
    (Z : PlanarGaloisInertiaModel F (G := G))
    (hall : ∀ B, Z.visibleSheets B = Set.univ) :
    PlanarHiddenInertiaRigidity Z := by
  apply planarHiddenInertiaRigidity_of_visibleSheetsDetectInertia
  intro B
  rw [hall B]
  exact
    visibleSheetsDetectInertia_univ_of_normalCore_eq_bot
      Z.H Z.normalClosure_coreFree

/--
The direct rigidity bridge for one planar map.  A nonzero collision
obstruction produces nontrivial global inertia, whereas planar
hidden-inertia rigidity forces every inertia group to be trivial.
-/
theorem obstructionIdeal_eq_bot_of_hiddenInertiaRigidity
    (Z : PlanarGaloisInertiaModel F (G := G))
    (hRigidity : PlanarHiddenInertiaRigidity Z) :
    obstructionIdeal F = ⊥ := by
  by_contra hObstruction
  have hNormalClosure :
      (⊤ : Subgroup G) ≠ ⊥ :=
    Z.obstruction_ne_bot_normalClosure_nontrivial hObstruction
  obtain ⟨B, hB⟩ :=
    Z.normalClosure_nontrivial_has_inertia hNormalClosure
  exact
    hB
      (inertiaGroup_eq_bot_of_planarHiddenInertiaRigidity
        Z hRigidity B)

/--
A universe-packaged witness that a planar map admits a finite Galois
normal-closure model satisfying hidden-inertia rigidity.
-/
def HasPlanarHiddenInertiaBridge
    (F : Fin 2 → PlanePolynomial) : Prop :=
  ∃ (G : Type u) (groupG : Group G),
    letI : Group G := groupG
    ∃ Z : PlanarGaloisInertiaModel F (G := G),
      PlanarHiddenInertiaRigidity Z

/-- A packaged hidden-inertia bridge kills the obstruction for one map. -/
theorem obstructionIdeal_eq_bot_of_hasHiddenInertiaBridge
    (h : HasPlanarHiddenInertiaBridge F) :
    obstructionIdeal F = ⊥ := by
  obtain ⟨G, groupG, hZ⟩ := h
  letI : Group G := groupG
  obtain ⟨Z, hRigidity⟩ := hZ
  exact
    obstructionIdeal_eq_bot_of_hiddenInertiaRigidity
      Z hRigidity

/--
The completed bridge to the theorem target: constructing a global normal
closure model with planar hidden-inertia rigidity for every planar Keller
map proves `PlanarVanishing`.
-/
theorem planarVanishing_of_hiddenInertiaRigidity
    (hBridge :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          HasPlanarHiddenInertiaBridge F) :
    PlanarVanishing := by
  intro F hF
  exact
    obstructionIdeal_eq_bot_of_hasHiddenInertiaBridge
      (hBridge F hF)

end GaloisBridge

end

end CollisionIdeals
