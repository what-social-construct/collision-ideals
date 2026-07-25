import CollisionIdeals.Planar.Inertia
import Mathlib.AlgebraicGeometry.Morphisms.Etale

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]
variable {M : PlanarNormalizedCover (F := F) (N := N)}

/--
The target-identification obligation for one planar Keller map: its two
coordinates are algebraically independent, so the abstract target
polynomial ring identifies with `ℂ[P,Q]`.

This is a theorem target, not currently derived from the concrete Jacobian
determinant in Lean.
-/
def PlanarKellerTargetImageBridge
    (F : Fin 2 → PlanePolynomial) : Prop :=
  IsPlanarKeller F →
    Function.Injective (coordinateAlgHom F)

/-- The target-image bridge supplies the corresponding affine-scheme isomorphism. -/
noncomputable def planarImageBaseIsoTarget_of_keller
    (F : Fin 2 → PlanePolynomial)
    (hTarget : PlanarKellerTargetImageBridge F)
    (hKeller : IsPlanarKeller F) :
    Spec (.of (planarImageAlgebra F)) ≅
      Spec (.of PlanePolynomial) :=
  planarImageBaseIsoTarget F (hTarget hKeller)

/--
The explicit scheme-theoretic Jacobian-criterion obligation for one planar
map: the Keller condition makes
`Spec ℂ[x,y] ⟶ Spec ℂ[P,Q]` étale.

This proposition is a theorem target.  The current mathlib API does not
derive it automatically from the concrete multivariate Jacobian
determinant used by this project.
-/
def PlanarKellerEtaleBridge
    (F : Fin 2 → PlanePolynomial) : Prop :=
  IsPlanarKeller F →
    IsEtale (planarSourceToImageBase F)

/--
The explicit valuation-center/boundary target.

For a family already proved to consist of the actual codimension-one
valuations of the normalized cover, it says that étaleness of the visible
affine-plane sheet places every intermediate-ramified center in the
deleted boundary of `X̄`.  The realization and center-compatibility proofs
are deliberately not hidden in this proposition.
-/
def PlanarValuationCenterBoundaryBridge
    (I : PlanarInertiaDivisorData M) : Prop :=
  IsEtale (planarSourceToImageBase F) →
    I.AllIntermediateRamificationHiddenInBoundary

/--
The two explicit étaleness bridges give the boundary statement used by
normalized hidden-inertia rigidity.
-/
theorem allIntermediateRamificationHiddenInBoundary
    (I : PlanarInertiaDivisorData M)
    (hKellerEtale : PlanarKellerEtaleBridge F)
    (hRamification :
      PlanarValuationCenterBoundaryBridge I)
    (hKeller : IsPlanarKeller F) :
    I.AllIntermediateRamificationHiddenInBoundary :=
  hRamification (hKellerEtale hKeller)

end

end CollisionIdeals
