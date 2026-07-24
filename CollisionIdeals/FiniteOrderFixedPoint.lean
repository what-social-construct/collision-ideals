import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.Centroid

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open Affine

/--
Every finite-order affine automorphism in characteristic zero has a fixed
point.  The fixed point is the centroid of one finite orbit.

For polynomial automorphisms of the affine plane, the missing extra step
is to conjugate the finite-order action to an affine one.
-/
theorem affineEquiv_exists_fixedPoint_of_isOfFinOrder
    {k V : Type*} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V]
    (e : V ≃ᵃ[k] V)
    (he : IsOfFinOrder e) :
    ∃ x : V, e x = x := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp he
  let p : ℕ → V := fun i ↦ (e ^ i) 0
  let w : ℕ → k := (Finset.range n).centroidWeights k
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hw : ∑ i ∈ Finset.range n, w i = 1 :=
    (Finset.range n).sum_centroidWeights_eq_one_of_card_ne_zero k
      (by simpa)
  let x := (Finset.range n).affineCombination k p w
  refine ⟨x, ?_⟩
  rw [show x = (Finset.range n).affineCombination k p w by rfl]
  change
    e.toAffineMap ((Finset.range n).affineCombination k p w) =
      (Finset.range n).affineCombination k p w
  rw [Finset.map_affineCombination (Finset.range n) p w hw e.toAffineMap]
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp only [Function.comp_apply, p, w, Finset.centroidWeights_apply]
  have happ (i : ℕ) :
      e.toAffineMap ((e ^ i) 0) = (e ^ (i + 1)) 0 := by
    change e ((e ^ i) 0) = (e ^ (i + 1)) 0
    rw [pow_succ', AffineEquiv.coe_mul]
    rfl
  simp_rw [happ]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [hpow, AffineEquiv.coe_one, id_eq, pow_zero]

end

end CollisionIdeals
