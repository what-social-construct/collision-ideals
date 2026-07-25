import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

set_option autoImplicit false

namespace CollisionIdeals

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable (B E : Type u)
variable [CommRing B] [CommRing E] [Algebra B E]

/-- The integral closure of the affine base ring `B` in an overring `E`. -/
abbrev normalizedCoordinateRing :=
  integralClosure B E

/--
The affine relative integral-closure model `Spec (integralClosure B E)`.

Under the usual domain, field-extension, and birational hypotheses this is
the normalization of `Spec B` in `E`; the generic definition intentionally
does not assert those hypotheses.
-/
def normalizedAffineModel : Scheme :=
  Spec (.of (normalizedCoordinateRing B E))

/-- The canonical morphism from the relative integral-closure model to `Spec B`. -/
def normalizedModelToBase :
    normalizedAffineModel B E ⟶ Spec (.of B) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap B (normalizedCoordinateRing B E)))

variable {B E}
variable (E' : Type u) [CommRing E'] [Algebra B E']

/--
An algebra homomorphism `E →ₐ[B] E'` restricts functorially to the two
integral closures over `B`.
-/
def normalizationMap (f : E →ₐ[B] E') :
    normalizedCoordinateRing B E →ₐ[B] normalizedCoordinateRing B E' :=
  f.mapIntegralClosure

@[simp]
theorem normalizationMap_coe
    (f : E →ₐ[B] E')
    (x : normalizedCoordinateRing B E) :
    ((normalizationMap E' f x :
      normalizedCoordinateRing B E') : E') = f (x : E) :=
  rfl

/-- Restriction to integral closures preserves injectivity. -/
theorem normalizationMap_injective
    (f : E →ₐ[B] E')
    (hf : Function.Injective f) :
    Function.Injective (normalizationMap E' f) := by
  intro x y hxy
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val hxy

/--
Contravariantly, an embedding of overrings makes the larger relative
integral-closure model dominate the smaller one.
-/
def normalizationDomination (f : E →ₐ[B] E') :
    normalizedAffineModel B E' ⟶ normalizedAffineModel B E :=
  Spec.map
    (CommRingCat.ofHom
      (normalizationMap E' f).toRingHom)

/-- The domination morphism is compatible with both structure maps to the base. -/
theorem normalizationDomination_comp_toBase
    (f : E →ₐ[B] E') :
    normalizationDomination E' f ≫ normalizedModelToBase B E =
      normalizedModelToBase B E' := by
  unfold normalizationDomination normalizedModelToBase
  rw [← Spec.map_comp]
  congr 1
  ext b
  simp [normalizationMap]

variable (A : Type u) [CommRing A]
variable [Algebra B A] [Algebra A E] [IsScalarTower B A E]
variable [IsIntegralClosure A A E]

/--
If `A` is integrally closed in `E`, every element of the integral closure
of `B` in `E` belongs canonically to `A`.

In the planar application, `A = ℂ[x,y]` and `E = ℂ(x,y)`.
-/
noncomputable def normalizationToIntermediate :
    normalizedCoordinateRing B E →ₐ[B] A where
  toFun x :=
    IsIntegralClosure.mk' A (x : E)
      (IsIntegral.tower_top (A := A) x.property)
  map_one' := by
    apply IsIntegralClosure.algebraMap_injective A A E
    simp
  map_mul' x y := by
    apply IsIntegralClosure.algebraMap_injective A A E
    simp
  map_zero' := by
    apply IsIntegralClosure.algebraMap_injective A A E
    simp
  map_add' x y := by
    apply IsIntegralClosure.algebraMap_injective A A E
    simp
  commutes' b := by
    apply IsIntegralClosure.algebraMap_injective A A E
    rw [IsIntegralClosure.algebraMap_mk']
    exact IsScalarTower.algebraMap_apply B A E b

@[simp]
theorem algebraMap_normalizationToIntermediate
    (x : normalizedCoordinateRing B E) :
    algebraMap A E
        (normalizationToIntermediate (B := B) (E := E) (A := A) x) =
      (x : E) :=
  IsIntegralClosure.algebraMap_mk' (R := A) A (x : E)
    (IsIntegral.tower_top (A := A) x.property)

/-- The canonical map from the normalization ring to the intermediate ring is injective. -/
theorem normalizationToIntermediate_injective :
    Function.Injective
      (normalizationToIntermediate (B := B) (E := E) (A := A)) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg (algebraMap A E) hxy
  simpa using h

/--
The canonical candidate for the intermediate open immersion
`Spec A ⟶ Norm_E(Spec B)`.

That this morphism is an open immersion is a separate geometric statement.
-/
def intermediateToNormalization :
    Spec (.of A) ⟶ normalizedAffineModel B E :=
  Spec.map
    (CommRingCat.ofHom
      (normalizationToIntermediate
        (B := B) (E := E) (A := A)).toRingHom)

/-- The intermediate model and normalization have the same map to the affine base. -/
theorem intermediateToNormalization_comp_toBase :
    intermediateToNormalization (B := B) (E := E) (A := A) ≫
        normalizedModelToBase B E =
      Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
  unfold intermediateToNormalization normalizedModelToBase
  rw [← Spec.map_comp]
  congr 1
  ext b
  simp

end

end CollisionIdeals
