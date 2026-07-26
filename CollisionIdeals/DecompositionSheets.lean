import CollisionIdeals.InertiaQuotient
import Mathlib.GroupTheory.DoubleCoset

set_option autoImplicit false

namespace CollisionIdeals

noncomputable section

open scoped Pointwise

universe u

variable {G : Type u} [Group G]

/--
The double-coset sheet classes `D \ G / H`.

For a Galois extension with decomposition group `D` and intermediate
fixing subgroup `H`, the standard valuation-theoretic prime classification
identifies these classes with primes of the intermediate normalization
above the selected base prime.  With the convention that `g` represents
the contraction of `g⁻¹E` to the fixed field `N^H`, the associated index
is `[I : I ∩ gHg⁻¹]`.  This definition records the group side; the
geometric identification is a separate bridge.
-/
abbrev DecompositionSheetClasses (D H : Subgroup G) :=
  DoubleCoset.Quotient (D : Set G) (H : Set G)

/-- The inertia index attached to an individual sheet of `G/H`. -/
noncomputable def inertiaIndexAtSheet
    (I H : Subgroup G)
    (s : GaloisSheets H) : ℕ :=
  (MulAction.stabilizer G s).relIndex I

/-- Index one is exactly trivial inertia action on the selected sheet. -/
theorem inertiaIndexAtSheet_eq_one_iff
    (I H : Subgroup G)
    (s : GaloisSheets H) :
    inertiaIndexAtSheet I H s = 1 ↔
      InertiaInvisibleAt I H s := by
  unfold inertiaIndexAtSheet
  rw [Subgroup.relIndex_eq_one,
    inertiaInvisibleAt_iff_le_stabilizer]

/--
Inertia has index one on every sheet exactly when it lies in the normal
core of the intermediate subgroup.
-/
theorem forall_inertiaIndexAtSheet_eq_one_iff_le_normalCore
    (I H : Subgroup G) :
    (∀ s : GaloisSheets H,
      inertiaIndexAtSheet I H s = 1) ↔
      I ≤ H.normalCore := by
  rw [← inertiaInvisibleOn_univ_iff_le_normalCore I H]
  simp only [InertiaInvisibleOn, Set.mem_univ, forall_const,
    inertiaIndexAtSheet_eq_one_iff]

/--
The inertia index at the sheet represented by `gH`:

`[J : J ∩ gHg⁻¹]`,

where `J` is first included from the decomposition group `D` into `G`.
-/
noncomputable def inertiaIndexAtRepresentative
    {D : Subgroup G}
    (J : Subgroup D)
    (H : Subgroup G)
    (g : G) : ℕ :=
  inertiaQuotientIndex
    (J.map D.subtype)
    (H.map (MulAut.conj g).toMonoidHom)

theorem inertiaIndexAtRepresentative_eq_stabilizer_relIndex
    {D : Subgroup G}
    (J : Subgroup D)
    (H : Subgroup G)
    (g : G) :
    inertiaIndexAtRepresentative J H g =
      (MulAction.stabilizer D
        (g • ((1 : G) : GaloisSheets H))).relIndex J := by
  let s : GaloisSheets H :=
    g • ((1 : G) : GaloisSheets H)
  have hstabilizer :
      MulAction.stabilizer D s =
        (MulAction.stabilizer G s).comap D.subtype := by
    ext d
    rfl
  symm
  calc
    (MulAction.stabilizer D s).relIndex J =
        ((MulAction.stabilizer G s).comap D.subtype).relIndex J := by
          rw [hstabilizer]
    _ = (MulAction.stabilizer G s).relIndex (J.map D.subtype) :=
      Subgroup.relIndex_comap
        (MulAction.stabilizer G s) D.subtype J
    _ = (H.map (MulAut.conj g).toMonoidHom).relIndex
          (J.map D.subtype) := by
      rw [show s = g • ((1 : G) : GaloisSheets H) from rfl,
        MulAction.stabilizer_smul_eq_stabilizer_map_conj,
        MulAction.stabilizer_quotient]
    _ = inertiaIndexAtRepresentative J H g := rfl

/-- The representative formula agrees with the stabilizer index of its sheet. -/
theorem inertiaIndexAtRepresentative_eq_inertiaIndexAtSheet
    {D : Subgroup G}
    (J : Subgroup D)
    (H : Subgroup G)
    (g : G) :
    inertiaIndexAtRepresentative J H g =
      inertiaIndexAtSheet (J.map D.subtype) H
        (g • ((1 : G) : GaloisSheets H)) := by
  unfold inertiaIndexAtRepresentative inertiaIndexAtSheet
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_quotient]
  rfl

/-- Representative index one is equivalent to inertia fixing that sheet. -/
theorem inertiaIndexAtRepresentative_eq_one_iff
    {D : Subgroup G}
    (J : Subgroup D)
    (H : Subgroup G)
    (g : G) :
    inertiaIndexAtRepresentative J H g = 1 ↔
      InertiaInvisibleAt (J.map D.subtype) H
        (g • ((1 : G) : GaloisSheets H)) := by
  rw [inertiaIndexAtRepresentative_eq_inertiaIndexAtSheet,
    inertiaIndexAtSheet_eq_one_iff]

/--
Normality of inertia inside the decomposition group makes the index
constant along the left `D`-orbit of a sheet.
-/
theorem inertiaIndexAtRepresentative_left_mul
    {D : Subgroup G}
    (J : Subgroup D)
    [J.Normal]
    (H : Subgroup G)
    (d : D)
    (g : G) :
    inertiaIndexAtRepresentative J H ((d : G) * g) =
      inertiaIndexAtRepresentative J H g := by
  rw [inertiaIndexAtRepresentative_eq_stabilizer_relIndex,
    inertiaIndexAtRepresentative_eq_stabilizer_relIndex]
  have hsmul :
      (((d : G) * g) • ((1 : G) : GaloisSheets H)) =
        d • (g • ((1 : G) : GaloisSheets H)) := by
    change
      (((d : G) * g) • ((1 : G) : GaloisSheets H)) =
        (d : G) • (g • ((1 : G) : GaloisSheets H))
    rw [mul_smul]
  rw [hsmul]
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hJ :
      J.map (MulAut.conj d).toMonoidHom = J := by
    simpa only [Subgroup.pointwise_smul_def] using
      (Subgroup.Normal.conj_smul_eq_self d J)
  conv_lhs =>
    rhs
    rw [← hJ]
  exact
    Subgroup.relIndex_map_map_of_injective
      (MulAction.stabilizer D
        (g • ((1 : G) : GaloisSheets H)))
      J
      (MulAut.conj d).injective

/-- Multiplying a representative on the right by `H` does not change its index. -/
theorem inertiaIndexAtRepresentative_right_mul
    {D : Subgroup G}
    (J : Subgroup D)
    (H : Subgroup G)
    (g : G)
    (h : H) :
    inertiaIndexAtRepresentative J H (g * (h : G)) =
      inertiaIndexAtRepresentative J H g := by
  rw [inertiaIndexAtRepresentative_eq_inertiaIndexAtSheet,
    inertiaIndexAtRepresentative_eq_inertiaIndexAtSheet]
  congr 1
  change
    (g * (h : G)) • ((1 : G) : GaloisSheets H) =
      g • ((1 : G) : GaloisSheets H)
  rw [mul_smul]
  have hh :
      (h : G) • ((1 : G) : GaloisSheets H) =
        ((1 : G) : GaloisSheets H) := by
    rw [← MulAction.mem_stabilizer_iff,
      MulAction.stabilizer_quotient]
    exact h.property
  rw [hh]

/--
The well-defined inertia index on a double-coset class `D \ G / H`.

Normality of `J` in `D` is exactly what makes the representative formula
constant under the left `D`-action; right `H`-invariance is automatic.
-/
noncomputable def inertiaIndexAtDoubleCoset
    (D : Subgroup G)
    (J : Subgroup D)
    [J.Normal]
    (H : Subgroup G) :
    DecompositionSheetClasses D H → ℕ :=
  fun q =>
    Quotient.liftOn q
      (inertiaIndexAtRepresentative J H)
      (fun a b hab => by
        change
          DoubleCoset.setoid (D : Set G) (H : Set G) a b
          at hab
        rw [DoubleCoset.rel_iff] at hab
        obtain ⟨d, hd, h, hh, rfl⟩ := hab
        let d' : D := ⟨d, hd⟩
        let h' : H := ⟨h, hh⟩
        exact
          ((inertiaIndexAtRepresentative_right_mul
              J H (d * a) h').trans
              (inertiaIndexAtRepresentative_left_mul
                J H d' a)).symm)

@[simp]
theorem inertiaIndexAtDoubleCoset_mk
    (D : Subgroup G)
    (J : Subgroup D)
    [J.Normal]
    (H : Subgroup G)
    (g : G) :
    inertiaIndexAtDoubleCoset D J H
        (DoubleCoset.mk D H g) =
      inertiaIndexAtRepresentative J H g :=
  rfl

/--
For a core-free intermediate subgroup, every nontrivial normal inertia
subgroup gives a ramified double-coset class.
-/
theorem exists_doubleCoset_one_lt_inertiaIndex
    [Finite G]
    (D : Subgroup G)
    (J : Subgroup D)
    [J.Normal]
    (H : Subgroup G)
    (hcore : H.normalCore = ⊥)
    (hJ : J ≠ ⊥) :
    ∃ q : DecompositionSheetClasses D H,
      1 < inertiaIndexAtDoubleCoset D J H q := by
  have hJmap : J.map D.subtype ≠ ⊥ := by
    intro hmap
    exact hJ
      ((Subgroup.map_eq_bot_iff_of_injective
        J D.subtype_injective).mp hmap)
  obtain ⟨g, hg⟩ :=
    exists_conjugate_one_lt_inertiaQuotientIndex
      (J.map D.subtype) H hcore hJmap
  exact ⟨DoubleCoset.mk D H g, hg⟩

end

end CollisionIdeals
