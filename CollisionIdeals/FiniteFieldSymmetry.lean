import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

universe u v

variable {K : Type u} {L : Type v}
variable [Field K] [Field L] [Algebra K L]

/--
A self-embedding of a finite field extension is automatically bijective.

This is the function-field step that turns a finite geometric
correspondence into a symmetry.
-/
theorem finiteDimensional_algHom_bijective
    [FiniteDimensional K L]
    (σ : L →ₐ[K] L) :
    Function.Bijective σ :=
  AlgHom.bijective σ

/-- Upgrade a self-embedding of a finite field extension to an automorphism. -/
def finiteDimensionalAlgEquivOfAlgHom
    [FiniteDimensional K L]
    (σ : L →ₐ[K] L) :
    L ≃ₐ[K] L :=
  AlgEquiv.ofBijective σ (finiteDimensional_algHom_bijective σ)

@[simp]
theorem finiteDimensionalAlgEquivOfAlgHom_apply
    [FiniteDimensional K L]
    (σ : L →ₐ[K] L)
    (x : L) :
    finiteDimensionalAlgEquivOfAlgHom σ x = σ x := by
  rfl

/--
The automorphism group of a finite field extension is finite, so every
field automorphism has finite order.
-/
theorem finiteDimensional_algEquiv_isOfFinOrder
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    IsOfFinOrder σ := by
  letI : Finite (L →ₐ[K] L) := inferInstance
  letI : Finite (L ≃ₐ[K] L) :=
    Finite.of_injective
      (fun e : L ≃ₐ[K] L ↦ e.toAlgHom)
      (by
        intro e₁ e₂ h
        ext x
        exact DFunLike.congr_fun h x)
  exact isOfFinOrder_of_finite σ

/--
Combining the two preceding steps, every self-embedding of a finite field
extension determines a finite-order automorphism.
-/
theorem finiteDimensionalAlgEquivOfAlgHom_isOfFinOrder
    [FiniteDimensional K L]
    (σ : L →ₐ[K] L) :
    IsOfFinOrder (finiteDimensionalAlgEquivOfAlgHom σ) :=
  finiteDimensional_algEquiv_isOfFinOrder _

end

end CollisionIdeals
