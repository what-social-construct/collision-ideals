import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.RingTheory.Ideal.Maps

/-!
# Boundary principal parts

This file gives the stable commutative-algebra object used by the global
boundary-coherence formulation in the paper.  It uses mathlib's actual local
cohomology functor, defined as a filtered colimit of Ext modules.

The ramification-supported principal-parts and uniform-annihilator objects
belong to the prospective finite-control strategy and are kept in
`CollisionIdeals.Planar.PrincipalPartsStrategy`.
-/

set_option autoImplicit false

open CategoryTheory

namespace CollisionIdeals

noncomputable section

universe u

variable (R : Type u) [CommRing R]

/-- First local cohomology of the ring with support in a boundary ideal. -/
def BoundaryPrincipalParts (J : Ideal R) : ModuleCat R :=
  (localCohomology J 1).obj (ModuleCat.of R R)

/--
Boundary coherence for an affine open complement: the first local-cohomology
module is finite over the ambient affine ring.  In the planar Zariski--Main
factorization this is the strong target that forces the entire deleted
boundary to disappear; that geometric implication is kept separate from
this algebraic definition.
-/
def BoundaryCoherence (J : Ideal R) : Prop :=
  Module.Finite R (BoundaryPrincipalParts R J)

/-- Boundary principal parts depend only on the radical of the support ideal. -/
def boundaryPrincipalPartsIsoOfSameRadical
    [IsNoetherian R R] {J K : Ideal R}
    (h : J.radical = K.radical) :
    BoundaryPrincipalParts R J ≅ BoundaryPrincipalParts R K :=
  (localCohomology.isoOfSameRadical h 1).app (ModuleCat.of R R)

end

end CollisionIdeals
