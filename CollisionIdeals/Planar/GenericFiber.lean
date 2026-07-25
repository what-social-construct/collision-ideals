import CollisionIdeals.OffDiagonalScheme
import CollisionIdeals.Planar.Normalization
import Mathlib.RingTheory.Localization.BaseChange

set_option autoImplicit false

namespace CollisionIdeals

open scoped TensorProduct

noncomputable section

/--
The canonical map from the generic source tensor algebra to the source
function field:

`K ⊗_B A ⟶ L`, `k ⊗ a ↦ k a`.

Here `B = ℂ[P,Q]`, `K = Frac(B)`, `A = ℂ[x,y]`, and `L = Frac(A)`.
-/
noncomputable def planarGenericSourceTensorMap
    (F : Fin 2 → PlanePolynomial) :
    (PlanarBaseFunctionField F ⊗[planarImageAlgebra F]
      PlanePolynomial) →ₐ[PlanarBaseFunctionField F]
        PlaneFunctionField :=
  Algebra.TensorProduct.lift
    (Algebra.ofId
      (PlanarBaseFunctionField F) PlaneFunctionField)
    (IsScalarTower.toAlgHom
      (planarImageAlgebra F) PlanePolynomial PlaneFunctionField)
    fun _ _ => mul_comm _ _

@[simp]
theorem planarGenericSourceTensorMap_tmul
    (F : Fin 2 → PlanePolynomial)
    (k : PlanarBaseFunctionField F)
    (a : PlanePolynomial) :
    planarGenericSourceTensorMap F (k ⊗ₜ a) =
      algebraMap (PlanarBaseFunctionField F) PlaneFunctionField k *
        algebraMap PlanePolynomial PlaneFunctionField a := by
  simp [planarGenericSourceTensorMap]

/--
The canonical map `K ⊗_B A ⟶ L` is always injective.

Mathlib identifies the source with the localization of `A` at the image of
the non-zero-divisors of `B`.  Its canonical map into `Frac(A)` is
injective because `A` is a domain.
-/
theorem planarGenericSourceTensorMap_injective
    (F : Fin 2 → PlanePolynomial) :
    Function.Injective (planarGenericSourceTensorMap F) := by
  let B := planarImageAlgebra F
  let A := PlanePolynomial
  let K := PlanarBaseFunctionField F
  let T := K ⊗[B] A
  letI : Algebra A T :=
    Algebra.TensorProduct.rightAlgebra
  letI :
      IsLocalization
        (Algebra.algebraMapSubmonoid A
          (nonZeroDivisors B)) T :=
    IsLocalization.tensorRight K (nonZeroDivisors B)
  apply
    IsLocalization.injective_of_map_algebraMap_zero
      (M := Algebra.algebraMapSubmonoid A
        (nonZeroDivisors B))
      T (planarGenericSourceTensorMap F).toRingHom
  intro a ha
  have haL :
      algebraMap PlanePolynomial PlaneFunctionField a = 0 := by
    change
      planarGenericSourceTensorMap F
          ((1 : PlanarBaseFunctionField F) ⊗ₜ[planarImageAlgebra F]
            a) = 0 at ha
    simpa only [planarGenericSourceTensorMap_tmul,
      map_one, one_mul] using ha
  have ha0 : a = 0 := by
    apply
      (FaithfulSMul.algebraMap_injective
        A PlaneFunctionField)
    simpa only [map_zero] using haL
  subst a
  exact map_zero (algebraMap A T)

/--
If `K ⊂ L` is trivial, the canonical map `K ⊗_B A ⟶ L` is surjective.
-/
theorem planarGenericSourceTensorMap_surjective
    (F : Fin 2 → PlanePolynomial)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    Function.Surjective (planarGenericSourceTensorMap F) := by
  intro z
  obtain ⟨k, hk⟩ := hTrivial z
  refine ⟨k ⊗ₜ (1 : PlanePolynomial), ?_⟩
  simpa [planarGenericSourceTensorMap] using hk

/--
The concrete generic-source-fiber calculation in generic degree one:

`K ⊗_B A ≃ₐ[K] L`.
-/
noncomputable def planarGenericSourceTensorEquiv
    (F : Fin 2 → PlanePolynomial)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    (PlanarBaseFunctionField F ⊗[planarImageAlgebra F]
      PlanePolynomial) ≃ₐ[PlanarBaseFunctionField F]
        PlaneFunctionField :=
  AlgEquiv.ofBijective
    (planarGenericSourceTensorMap F)
    ⟨planarGenericSourceTensorMap_injective F,
      planarGenericSourceTensorMap_surjective F hTrivial⟩

@[simp]
theorem planarGenericSourceTensorEquiv_tmul
    (F : Fin 2 → PlanePolynomial)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F)
    (k : PlanarBaseFunctionField F)
    (a : PlanePolynomial) :
    planarGenericSourceTensorEquiv F hTrivial (k ⊗ₜ a) =
      algebraMap (PlanarBaseFunctionField F) PlaneFunctionField k *
        algebraMap PlanePolynomial PlaneFunctionField a :=
  planarGenericSourceTensorMap_tmul F k a

/--
The generic-fiber bridge used after normalization:

if a planar Keller map has trivial function-field extension
`ℂ(P,Q) ⊂ ℂ(x,y)`, then its off-diagonal collision scheme is empty.

Geometrically, a nonempty component of the étale self-fiber product has
open image under the first projection and therefore contributes another
generic sheet.  This definition isolates that standard geometric lemma;
it does not add it as an axiom.
-/
def PlanarGenericDegreeOneExcludesOffDiagonal : Prop :=
  ∀ (F : Fin 2 → PlanePolynomial),
    IsPlanarKeller F →
      PlanarFunctionFieldExtensionTrivial F →
        CollisionOffDiagonalVanishing F

/--
The generic-degree-one bridge kills the obstruction ideal for one planar
Keller map.
-/
theorem obstructionIdeal_eq_bot_of_planarFunctionField_trivial
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal)
    (F : Fin 2 → PlanePolynomial)
    (hKeller : IsPlanarKeller F)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    obstructionIdeal F = ⊥ :=
  (collisionOffDiagonalVanishing_iff_obstructionIdeal_eq_bot F).mp
    (hGeneric F hKeller hTrivial)

/--
Equivalently, the canonical collision-to-diagonal map has zero kernel.
-/
theorem collisionDiagonalMap_ker_eq_bot_of_planarFunctionField_trivial
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal)
    (F : Fin 2 → PlanePolynomial)
    (hKeller : IsPlanarKeller F)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    RingHom.ker (collisionDiagonalMap F) = ⊥ := by
  rw [collisionDiagonalMap_ker]
  exact
    obstructionIdeal_eq_bot_of_planarFunctionField_trivial
      hGeneric F hKeller hTrivial

/--
Equivalently, the collision and diagonal ideals agree.
-/
theorem relationIdeal_eq_diagonalIdeal_of_planarFunctionField_trivial
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal)
    (F : Fin 2 → PlanePolynomial)
    (hKeller : IsPlanarKeller F)
    (hTrivial : PlanarFunctionFieldExtensionTrivial F) :
    relationIdeal F =
      diagonalIdeal (R := ℂ) (ι := Fin 2) :=
  (obstructionIdeal_eq_bot_iff F).mp
    (obstructionIdeal_eq_bot_of_planarFunctionField_trivial
      hGeneric F hKeller hTrivial)

/--
The exact end-to-end planar reduction.

Once finite-completion/open-immersion inputs, normalization rigidity, and
the generic-fiber collision lemma are supplied, planar obstruction
vanishing follows formally.
-/
theorem planarVanishing_of_normalizationRigidity
    (hFinite :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          IsPlanarFiniteCompletion F)
    (hOpen :
      ∀ (F : Fin 2 → PlanePolynomial),
        IsPlanarKeller F →
          IsPlanarIntermediateOpen F)
    (hRigidity : PlanarNormalizationRigidity)
    (hGeneric : PlanarGenericDegreeOneExcludesOffDiagonal) :
    PlanarVanishing := by
  intro F hKeller
  exact
    obstructionIdeal_eq_bot_of_planarFunctionField_trivial
      hGeneric F hKeller
        (hRigidity F hKeller
          (hFinite F hKeller)
          (hOpen F hKeller))

end

end CollisionIdeals
