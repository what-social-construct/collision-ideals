import CollisionIdeals.General.Normalization.Polynomial
import CollisionIdeals.General.FiberProduct.UniversalProperty

/-!
# Galois collision map pairs for polynomial maps

This file constructs, in arbitrary dimension, the collision map pair attached
to two conjugate polynomial sheets in a marked normal closure.  The
construction is independent of the planar secant argument: it supplies the
ground-field algebra on the normal closure, restricts the existing conjugate
function-field embeddings to polynomial source maps, proves agreement on the
coordinate-image algebra, and packages the ordered pair `(g, σg)` as a
`CollisionMapPair`.

Dimension-specific consequences, such as factoring a moved planar pair
through the planar off-diagonal quotient, belong in the corresponding
specialization module.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CollisionIdeals

noncomputable section

open MvPolynomial

universe u

variable {k : Type u} [Field k]
variable {n : ℕ}
variable {F : PolynomialSelfMap k n}
variable {N : Type u} [Field N]
variable [Algebra (PolynomialMapBaseFunctionField F) N]

/-- The ground-field algebra structure on the normal closure induced through
the base function field. -/
noncomputable def polynomialNormalExtensionGroundAlgebra : Algebra k N :=
  ((algebraMap (PolynomialMapBaseFunctionField F) N).comp
    (algebraMap k (PolynomialMapBaseFunctionField F))).toAlgebra

/-- Compatibility of the ground-field action with the action through the
coordinate-image algebra. -/
theorem polynomialNormalExtensionGroundImageTower :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    IsScalarTower k (PolynomialImageAlgebra F) N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra k N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change
    algebraMap (PolynomialMapBaseFunctionField F) N
        (algebraMap k (PolynomialMapBaseFunctionField F) c) =
      algebraMap (PolynomialMapBaseFunctionField F) N
        (algebraMap (PolynomialImageAlgebra F)
          (PolynomialMapBaseFunctionField F)
          (algebraMap k (PolynomialImageAlgebra F) c))
  rw [IsScalarTower.algebraMap_apply k (PolynomialImageAlgebra F)
    (PolynomialMapBaseFunctionField F)]

/-- The polynomial source map for the conjugate sheet `g`, retained as a map
over the actual coordinate-image algebra. -/
noncomputable def polynomialConjugateSourceMapOverImage
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    PolynomialSourceCoordinateRing k n →ₐ[PolynomialImageAlgebra F] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  exact
    (polynomialConjugateNormalClosureEmbeddingOverBase D g).comp
      (IsScalarTower.toAlgHom
        (PolynomialImageAlgebra F)
        (PolynomialSourceCoordinateRing k n)
        (PolynomialMapSourceFunctionField F))

@[simp]
theorem polynomialConjugateSourceMapOverImage_apply
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) (p : PolynomialSourceCoordinateRing k n) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    polynomialConjugateSourceMapOverImage D g p =
      g (D.embedding
        (algebraMap (PolynomialSourceCoordinateRing k n)
          (PolynomialMapSourceFunctionField F) p)) := by
  rfl

/-- Any two conjugate polynomial source maps agree on every output
coordinate of `F`. -/
theorem polynomialConjugateSourceMapOverImage_apply_F_eq
    (D : PolynomialNormalClosureData F N)
    (g h : D.galoisGroup) (j : Fin n) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    polynomialConjugateSourceMapOverImage D g (F j) =
      polynomialConjugateSourceMapOverImage D h (F j) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  let b : PolynomialImageAlgebra F :=
    ⟨F j, ⟨X j, coordinateAlgHom_X F j⟩⟩
  change
    polynomialConjugateSourceMapOverImage D g
        (algebraMap _ (PolynomialSourceCoordinateRing k n) b) =
      polynomialConjugateSourceMapOverImage D h
        (algebraMap _ (PolynomialSourceCoordinateRing k n) b)
  rw [(polynomialConjugateSourceMapOverImage D g).commutes,
    (polynomialConjugateSourceMapOverImage D h).commutes]

/-- The conjugate polynomial source map depends only on the right coset of
the intermediate fixing subgroup. -/
theorem polynomialConjugateSourceMapOverImage_right_mul
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup)
    (h : D.intermediateFixingSubgroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    polynomialConjugateSourceMapOverImage D
        (g * (h : D.galoisGroup)) =
      polynomialConjugateSourceMapOverImage D g := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  unfold polynomialConjugateSourceMapOverImage
  rw [polynomialConjugateNormalClosureEmbeddingOverBase_right_mul D g h]

/-- An element outside the stabilizer `gHg⁻¹` gives a genuinely distinct
conjugate polynomial sheet. -/
theorem polynomialConjugateSourceMapOverImage_ne_of_not_mem_conjugateFixingSubgroup
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hσ : σ ∉ D.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    polynomialConjugateSourceMapOverImage D g ≠
      polynomialConjugateSourceMapOverImage D (σ * g) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  intro hmaps
  apply hσ
  rw [Subgroup.mem_map_equiv]
  apply (IntermediateField.mem_fixingSubgroup_iff
    D.intermediateField _).mpr
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have hfull :
      (polynomialConjugateNormalClosureEmbeddingOverBase D g).toRingHom =
        (polynomialConjugateNormalClosureEmbeddingOverBase
          D (σ * g)).toRingHom := by
    apply IsFractionRing.ringHom_ext
      (A := PolynomialSourceCoordinateRing k n)
    intro p
    have hp := AlgHom.congr_fun hmaps p
    simpa only [polynomialConjugateSourceMapOverImage_apply] using hp
  have hx := RingHom.congr_fun hfull x
  change g (D.embedding x) = σ (g (D.embedding x)) at hx
  have hx' := congrArg g.symm hx
  simpa only [AlgEquiv.symm_apply_apply] using hx'.symm

/-- The conjugate polynomial source map, regarded as a ground-field algebra
map. -/
noncomputable def polynomialConjugateSourceMap
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    PolynomialSourceCoordinateRing k n →ₐ[k] N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra k N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsScalarTower k (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionGroundImageTower (F := F) (N := N)
  exact (polynomialConjugateSourceMapOverImage D g).restrictScalars k

@[simp]
theorem polynomialConjugateSourceMap_apply
    (D : PolynomialNormalClosureData F N)
    (g : D.galoisGroup) (p : PolynomialSourceCoordinateRing k n) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    polynomialConjugateSourceMap D g p =
      g (D.embedding
        (algebraMap (PolynomialSourceCoordinateRing k n)
          (PolynomialMapSourceFunctionField F) p)) := by
  rfl

/-- Distinctness over the image algebra remains distinctness after restricting
to the ground field. -/
theorem polynomialConjugateSourceMap_ne_of_not_mem_conjugateFixingSubgroup
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hσ : σ ∉ D.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    polynomialConjugateSourceMap D g ≠
      polynomialConjugateSourceMap D (σ * g) := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra k N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  intro hmaps
  apply
    polynomialConjugateSourceMapOverImage_ne_of_not_mem_conjugateFixingSubgroup
      D g σ hσ
  apply AlgHom.ext
  intro p
  exact AlgHom.congr_fun hmaps p

/-- The dimension-independent Galois collision map pair associated to the
ordered pair of conjugate sheets `(g, σg)`. -/
noncomputable def polynomialGaloisCollisionPair
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    CollisionMapPair F N := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra k N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  letI : IsScalarTower k (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionGroundImageTower (F := F) (N := N)
  exact
    { left := polynomialConjugateSourceMap D g
      right := polynomialConjugateSourceMap D (σ * g)
      agree := fun j =>
        polynomialConjugateSourceMapOverImage_apply_F_eq
          D g (σ * g) j }

@[simp]
theorem polynomialGaloisCollisionPair_left
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    (polynomialGaloisCollisionPair D g σ).left =
      polynomialConjugateSourceMap D g := by
  rfl

@[simp]
theorem polynomialGaloisCollisionPair_right
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    (polynomialGaloisCollisionPair D g σ).right =
      polynomialConjugateSourceMap D (σ * g) := by
  rfl

/-- The group-theoretic moved-sheet condition directly gives distinct source
maps in the Galois collision pair. -/
theorem polynomialGaloisCollisionPair_left_ne_right_of_not_mem
    (D : PolynomialNormalClosureData F N)
    (g σ : D.galoisGroup)
    (hσ : σ ∉ D.intermediateFixingSubgroup.map
      (MulAut.conj g).toMonoidHom) :
    letI : Algebra (PolynomialImageAlgebra F) N :=
      polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
    letI : Algebra k N :=
      polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
    (polynomialGaloisCollisionPair D g σ).left ≠
      (polynomialGaloisCollisionPair D g σ).right := by
  letI : Algebra (PolynomialImageAlgebra F) N :=
    polynomialNormalExtensionBaseAlgebra (F := F) (N := N)
  letI : Algebra k N :=
    polynomialNormalExtensionGroundAlgebra (F := F) (N := N)
  simpa only [polynomialGaloisCollisionPair_left,
    polynomialGaloisCollisionPair_right] using
      polynomialConjugateSourceMap_ne_of_not_mem_conjugateFixingSubgroup
        D g σ hσ

end

end CollisionIdeals
