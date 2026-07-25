import CollisionIdeals.Planar.ValuationInertia
import Mathlib.AlgebraicGeometry.Morphisms.Etale

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry

noncomputable section

variable {F : Fin 2 → PlanePolynomial}
variable {N : Type} [Field N]
variable [Algebra (PlanarBaseFunctionField F) N]
variable {M : PlanarNormalizedCover (F := F) (N := N)}

namespace PlanarValuationInertiaFamily

/--
There is no nontrivial divisorial inertia in the supplied exhaustive
valuation family.

Every member of `V.Divisor` carries nontrivial inertia by construction, so
emptiness is the type-correct formulation of trivial divisorial inertia.
-/
def NoNontrivialDivisorialInertia
    (V : PlanarValuationInertiaFamily M) : Prop :=
  IsEmpty V.Divisor

/--
The purity interface for the finite normal-closure model.

It promotes the absence of codimension-one inertia in an exhaustive
valuation family to étaleness of the whole finite normalization
`Norm_N(Y) ⟶ Y`.
-/
def DivisorialPurity
    (V : PlanarValuationInertiaFamily M) : Prop :=
  V.NoNontrivialDivisorialInertia →
    IsEtale
      (planarNormalizationInExtensionToBase
        (F := F) (N := N))

end PlanarValuationInertiaFamily

namespace PlanarNormalizedCover

/--
Finite-étale rigidity for the connected normal-closure cover of the affine
plane.

The cover is already finite by `M.finiteNormalClosureModel`, and its source
is integral because it is the normalization inside the field `N`.  This
interface records the remaining affine-plane fact that an étale such cover
is trivial.
-/
def FiniteEtaleRigidity
    (M : PlanarNormalizedCover (F := F) (N := N)) : Prop :=
  IsEtale
      (planarNormalizationInExtensionToBase
        (F := F) (N := N)) →
    M.normalClosure.ExtensionTrivial

end PlanarNormalizedCover

namespace PlanarValuationInertiaFamily

variable (V : PlanarValuationInertiaFamily M)

/--
Purity followed by finite-étale rigidity turns trivial divisorial inertia
into `N = K`.
-/
theorem normalClosureExtension_trivial_of_noNontrivialDivisorialInertia
    (hNoInertia : V.NoNontrivialDivisorialInertia)
    (hPurity : V.DivisorialPurity)
    (hFiniteEtaleRigidity : M.FiniteEtaleRigidity) :
    M.normalClosure.ExtensionTrivial :=
  hFiniteEtaleRigidity (hPurity hNoInertia)

/--
After purity and finite-étale rigidity give `N = K`, the distinguished
intermediate field is also trivial: `L = K`.
-/
theorem functionFieldExtension_trivial_of_noNontrivialDivisorialInertia
    (hNoInertia : V.NoNontrivialDivisorialInertia)
    (hPurity : V.DivisorialPurity)
    (hFiniteEtaleRigidity : M.FiniteEtaleRigidity) :
    PlanarFunctionFieldExtensionTrivial F :=
  M.normalClosure.functionFieldExtensionTrivial_of_extensionTrivial
    (V.normalClosureExtension_trivial_of_noNontrivialDivisorialInertia
      hNoInertia hPurity hFiniteEtaleRigidity)

end PlanarValuationInertiaFamily

end

end CollisionIdeals
