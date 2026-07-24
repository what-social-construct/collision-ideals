import CollisionIdeals.Planar
import Mathlib.GroupTheory.GroupAction.Quotient

set_option autoImplicit false

namespace CollisionIdeals

universe u

noncomputable section

section InertiaOnSheets

variable {G : Type u} [Group G]

/-- The sheets of the intermediate quotient associated with `H ≤ G`. -/
abbrev GaloisSheets (H : Subgroup G) :=
  G ⧸ H

/--
An inertia subgroup is invisible at a sheet when every inertia element fixes
that sheet.  In geometric applications this is the group-theoretic content
of the intermediate sheet being unramified.
-/
def InertiaInvisibleAt
    (I H : Subgroup G) (s : GaloisSheets H) : Prop :=
  ∀ i : I, (i : G) • s = s

/-- Inertia is invisible on every sheet belonging to a specified visible locus. -/
def InertiaInvisibleOn
    (I H : Subgroup G) (visible : Set (GaloisSheets H)) : Prop :=
  ∀ s, s ∈ visible → InertiaInvisibleAt I H s

/--
The visible sheets detect inertia if an inertia subgroup fixing all of them
must be trivial.
-/
def VisibleSheetsDetectInertia
    (H : Subgroup G) (visible : Set (GaloisSheets H)) : Prop :=
  ∀ I : Subgroup G, InertiaInvisibleOn I H visible → I = ⊥

theorem inertiaInvisibleAt_iff_le_stabilizer
    (I H : Subgroup G) (s : GaloisSheets H) :
    InertiaInvisibleAt I H s ↔
      I ≤ MulAction.stabilizer G s := by
  constructor
  · intro h g hg
    rw [MulAction.mem_stabilizer_iff]
    exact h ⟨g, hg⟩
  · intro h i
    exact
      (MulAction.mem_stabilizer_iff.mp
        (h i.property))

theorem inertiaInvisibleAt_baseSheet_iff
    (I H : Subgroup G) :
    InertiaInvisibleAt I H ((1 : G) : GaloisSheets H) ↔ I ≤ H := by
  rw [inertiaInvisibleAt_iff_le_stabilizer,
    MulAction.stabilizer_quotient]

/--
The stabilizer of the sheet `gH` is the conjugate `gHg⁻¹`.
-/
theorem inertiaInvisibleAt_conjugateSheet_iff
    (I H : Subgroup G) (g : G) :
    InertiaInvisibleAt I H
        (g • ((1 : G) : GaloisSheets H)) ↔
      I ≤ H.map (MulAut.conj g).toMonoidHom := by
  rw [inertiaInvisibleAt_iff_le_stabilizer,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_quotient]

/--
An inertia subgroup fixes every sheet of `G/H` exactly when it lies in the
normal core of `H`.
-/
theorem inertiaInvisibleOn_univ_iff_le_normalCore
    (I H : Subgroup G) :
    InertiaInvisibleOn I H Set.univ ↔ I ≤ H.normalCore := by
  rw [H.normalCore_eq_ker]
  constructor
  · intro h g hg
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro s
    change g • s = s
    exact h s (Set.mem_univ s) ⟨g, hg⟩
  · intro h s _ i
    have hi :
        (i : G) ∈
          (MulAction.toPermHom G (GaloisSheets H)).ker :=
      h i.property
    rw [MonoidHom.mem_ker] at hi
    have hs := Equiv.congr_fun hi s
    simpa using hs

/-- Core-free intermediate subgroups make the full sheet set detect inertia. -/
theorem visibleSheetsDetectInertia_univ_of_normalCore_eq_bot
    (H : Subgroup G) (hcore : H.normalCore = ⊥) :
    VisibleSheetsDetectInertia H Set.univ := by
  intro I hI
  apply le_bot_iff.mp
  rw [← hcore]
  exact (inertiaInvisibleOn_univ_iff_le_normalCore I H).mp hI

/--
In a core-free coset action, every nontrivial inertia subgroup moves at
least one sheet.
-/
theorem exists_sheet_moved_of_normalCore_eq_bot
    (I H : Subgroup G) (hcore : H.normalCore = ⊥)
    (hI : I ≠ ⊥) :
    ∃ s : GaloisSheets H, ¬ InertiaInvisibleAt I H s := by
  by_contra hAll
  have hInvisible : InertiaInvisibleOn I H Set.univ := by
    intro s _
    exact Classical.byContradiction fun hs ↦
      hAll ⟨s, hs⟩
  exact
    hI
      (visibleSheetsDetectInertia_univ_of_normalCore_eq_bot
        H hcore I hInvisible)

end InertiaOnSheets

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
