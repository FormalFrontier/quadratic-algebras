/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.NumberField
public import QuadraticAlgebras.Dedekind
public import QuadraticAlgebras.SqrtNegFive

/-!
# The class number of `ℚ(√-5)`

This file classifies the integral ideals of absolute norm at most two in the
ring of integers of `ℚ(√-5)`.  The unique ideal of norm two is obtained as the
kernel of reduction to `ZMod 2`; it is nonprincipal.  Combining this
classification with the Minkowski representative bound proves that the class
number is two.

The localization and basic-open calculations motivated by this example are
separate from the source-independent number-field theory developed here.
-/

public section

noncomputable section

open QuadraticAlgebra

namespace QuadraticAlgebra

/-- Reduction of `ℤ[√-5]` modulo the relation sending `√-5` to `1` in
`ZMod 2`. -/
@[expose]
def sqrtNegFiveModTwo : SqrtNegFiveOrder →+* ZMod 2 :=
  (QuadraticAlgebra.lift (R := ℤ) (A := ZMod 2)
    (a := (-5 : ℤ)) (b := 0) ⟨1, by decide⟩).toRingHom

/-- Reduction from `ℤ[√-5]` to `ZMod 2` is surjective. -/
theorem sqrtNegFiveModTwo_surjective :
    Function.Surjective sqrtNegFiveModTwo :=
  ZMod.ringHom_surjective sqrtNegFiveModTwo

/-- The distinguished ideal of `ℤ[√-5]` obtained as the kernel of reduction
to `ZMod 2`. -/
@[expose]
def sqrtNegFiveIdealTwo : Ideal SqrtNegFiveOrder :=
  RingHom.ker sqrtNegFiveModTwo

/-- The quotient of `ℤ[√-5]` by its distinguished norm-two ideal is
`ZMod 2`. -/
@[expose]
def quotientSqrtNegFiveIdealTwoEquiv :
    SqrtNegFiveOrder ⧸ sqrtNegFiveIdealTwo ≃+* ZMod 2 :=
  RingHom.quotientKerEquivOfSurjective sqrtNegFiveModTwo_surjective

/-- The integrally closed negative-five quadratic order is a Dedekind
domain. -/
instance : IsDedekindDomain SqrtNegFiveOrder :=
  QuadraticAlgebra.isDedekindDomain_of_isIntegrallyClosed

/-- The distinguished ideal of `ℤ[√-5]` has absolute norm two. -/
theorem absNorm_sqrtNegFiveIdealTwo :
    Ideal.absNorm sqrtNegFiveIdealTwo = 2 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr quotientSqrtNegFiveIdealTwoEquiv.toEquiv,
    Nat.card_zmod]

/-- On `ℤ[√-5]`, the algebra norm agrees with the quadratic-algebra norm. -/
theorem algebraNorm_eq_norm_sqrtNegFive (x : SqrtNegFiveOrder) :
    Algebra.norm ℤ x = QuadraticAlgebra.norm x := by
  rw [Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis (-5 : ℤ) 0),
    Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.norm_def]

/-- The distinguished norm-two ideal of `ℤ[√-5]` is not principal. -/
theorem not_isPrincipal_sqrtNegFiveIdealTwo :
    ¬ Submodule.IsPrincipal sqrtNegFiveIdealTwo := by
  rintro ⟨x, hx⟩
  have hnorm : (Algebra.norm ℤ x).natAbs = 2 := by
    calc
      (Algebra.norm ℤ x).natAbs =
          Ideal.absNorm (Ideal.span ({x} : Set SqrtNegFiveOrder)) :=
        (Ideal.absNorm_span_singleton x).symm
      _ = Ideal.absNorm sqrtNegFiveIdealTwo := by rw [hx]
      _ = 2 := absNorm_sqrtNegFiveIdealTwo
  rw [algebraNorm_eq_norm_sqrtNegFive] at hnorm
  have hnonneg : 0 ≤ QuadraticAlgebra.norm x := by
    rw [norm_int_negFive_eq]
    positivity
  have hnorm_two : QuadraticAlgebra.norm x = 2 := by
    omega
  rw [norm_int_negFive_eq] at hnorm_two
  have him : x.im = 0 := by
    nlinarith [sq_nonneg x.re, sq_nonneg x.im]
  rw [him] at hnorm_two
  norm_num at hnorm_two
  have hlo : -2 < x.re := by nlinarith [sq_nonneg x.re]
  have hhi : x.re < 2 := by nlinarith [sq_nonneg x.re]
  interval_cases x.re <;> norm_num at hnorm_two

/-- Every ideal of `ℤ[√-5]` of absolute norm two is the distinguished kernel
ideal. -/
theorem eq_sqrtNegFiveIdealTwo_of_absNorm_eq_two
    (I : Ideal SqrtNegFiveOrder) (hI : Ideal.absNorm I = 2) :
    I = sqrtNegFiveIdealTwo := by
  let hfinite : Finite (SqrtNegFiveOrder ⧸ I) :=
    (Ideal.absNorm_ne_zero_iff I).mp (by omega)
  let _ : Fintype (SqrtNegFiveOrder ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (SqrtNegFiveOrder ⧸ I) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
    exact hI
  let e : ZMod 2 ≃+* SqrtNegFiveOrder ⧸ I :=
    ZMod.ringEquivOfPrime _ (by decide) hcard
  let f : SqrtNegFiveOrder →+* ZMod 2 :=
    e.symm.toRingHom.comp (Ideal.Quotient.mk I)
  have hfomega : f (ω : SqrtNegFiveOrder) = 1 := by
    have hsquare : f (ω : SqrtNegFiveOrder) * f ω = 1 := by
      rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      norm_num [map_ofNat]
      decide
    have hne : f (ω : SqrtNegFiveOrder) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hsquare
      exact zero_ne_one hsquare
    simpa using ZMod.pow_card_sub_one_eq_one hne
  have hf : f = sqrtNegFiveModTwo := by
    apply RingHom.toIntAlgHom_injective
    apply QuadraticAlgebra.algHom_ext
    change f (ω : SqrtNegFiveOrder) = sqrtNegFiveModTwo ω
    rw [hfomega]
    rfl
  have hker : RingHom.ker f = I := by
    ext x
    constructor
    · intro hx
      have hxq : Ideal.Quotient.mk I x = 0 :=
        e.symm.injective (by simpa [f] using hx)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hxq
    · intro hx
      have hxq : Ideal.Quotient.mk I x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      simp [f, hxq]
  simpa [sqrtNegFiveIdealTwo, hf] using hker.symm

/-- The ring of integers of `ℚ(√-5)`. -/
abbrev SqrtNegFiveRingOfIntegers :=
  NumberField.RingOfIntegers SqrtNegFiveField

/-- Reduction of the ring of integers of `ℚ(√-5)` to `ZMod 2`. -/
@[expose]
def sqrtNegFiveRingOfIntegersModTwo :
    SqrtNegFiveRingOfIntegers →+* ZMod 2 :=
  sqrtNegFiveModTwo.comp sqrtNegFiveRingOfIntegersEquiv.symm.toRingHom

/-- Reduction of the ring of integers of `ℚ(√-5)` to `ZMod 2` is
surjective. -/
theorem sqrtNegFiveRingOfIntegersModTwo_surjective :
    Function.Surjective sqrtNegFiveRingOfIntegersModTwo :=
  sqrtNegFiveModTwo_surjective.comp
    sqrtNegFiveRingOfIntegersEquiv.symm.surjective

/-- The distinguished norm-two ideal in the ring of integers of `ℚ(√-5)`. -/
@[expose]
def sqrtNegFiveRingOfIntegersIdealTwo :
    Ideal SqrtNegFiveRingOfIntegers :=
  RingHom.ker sqrtNegFiveRingOfIntegersModTwo

/-- The quotient of the ring of integers of `ℚ(√-5)` by its distinguished
norm-two ideal is `ZMod 2`. -/
@[expose]
def quotientSqrtNegFiveRingOfIntegersIdealTwoEquiv :
    SqrtNegFiveRingOfIntegers ⧸ sqrtNegFiveRingOfIntegersIdealTwo ≃+* ZMod 2 :=
  RingHom.quotientKerEquivOfSurjective
    sqrtNegFiveRingOfIntegersModTwo_surjective

/-- The distinguished ideal in the ring of integers of `ℚ(√-5)` has absolute
norm two. -/
theorem absNorm_sqrtNegFiveRingOfIntegersIdealTwo :
    Ideal.absNorm sqrtNegFiveRingOfIntegersIdealTwo = 2 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr quotientSqrtNegFiveRingOfIntegersIdealTwoEquiv.toEquiv,
    Nat.card_zmod]

/-- Pulling back the distinguished ideal of the ring of integers recovers the
distinguished ideal of `ℤ[√-5]`. -/
theorem comap_sqrtNegFiveRingOfIntegersIdealTwo :
    sqrtNegFiveRingOfIntegersIdealTwo.comap
        sqrtNegFiveRingOfIntegersEquiv.toRingHom =
      sqrtNegFiveIdealTwo := by
  ext x
  simp [sqrtNegFiveRingOfIntegersIdealTwo,
    sqrtNegFiveRingOfIntegersModTwo, sqrtNegFiveIdealTwo]

/-- The distinguished norm-two ideal in the ring of integers of `ℚ(√-5)` is
not principal. -/
theorem not_isPrincipal_sqrtNegFiveRingOfIntegersIdealTwo :
    ¬ Submodule.IsPrincipal sqrtNegFiveRingOfIntegersIdealTwo := by
  intro hprincipal
  have hmapped := hprincipal.map_ringHom
    sqrtNegFiveRingOfIntegersEquiv.symm.toRingHom
  have hmap :
      sqrtNegFiveRingOfIntegersIdealTwo.map
          sqrtNegFiveRingOfIntegersEquiv.symm.toRingHom =
        sqrtNegFiveRingOfIntegersIdealTwo.comap
          sqrtNegFiveRingOfIntegersEquiv.toRingHom :=
    Ideal.map_symm sqrtNegFiveRingOfIntegersEquiv
  rw [hmap, comap_sqrtNegFiveRingOfIntegersIdealTwo] at hmapped
  exact not_isPrincipal_sqrtNegFiveIdealTwo hmapped

/-- Every ring homomorphism from the ring of integers of `ℚ(√-5)` to
`ZMod 2` is the distinguished reduction map. -/
theorem ringHom_eq_sqrtNegFiveRingOfIntegersModTwo
    (f : SqrtNegFiveRingOfIntegers →+* ZMod 2) :
    f = sqrtNegFiveRingOfIntegersModTwo := by
  let g : SqrtNegFiveOrder →+* ZMod 2 :=
    f.comp sqrtNegFiveRingOfIntegersEquiv.toRingHom
  have gomega : g (ω : SqrtNegFiveOrder) = 1 := by
    have hsquare : g (ω : SqrtNegFiveOrder) * g ω = 1 := by
      rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      norm_num [map_ofNat]
      decide
    have hne : g (ω : SqrtNegFiveOrder) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hsquare
      exact zero_ne_one hsquare
    simpa using ZMod.pow_card_sub_one_eq_one hne
  have hg : g = sqrtNegFiveModTwo := by
    apply RingHom.toIntAlgHom_injective
    apply QuadraticAlgebra.algHom_ext
    change g (ω : SqrtNegFiveOrder) = sqrtNegFiveModTwo ω
    rw [gomega]
    rfl
  ext y
  obtain ⟨x, rfl⟩ := sqrtNegFiveRingOfIntegersEquiv.surjective y
  have hxy := DFunLike.congr_fun hg x
  simpa [g, sqrtNegFiveRingOfIntegersModTwo] using hxy

/-- Every ideal of absolute norm two in the ring of integers of `ℚ(√-5)` is
the distinguished kernel ideal. -/
theorem eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_eq_two
    (I : Ideal SqrtNegFiveRingOfIntegers) (hI : Ideal.absNorm I = 2) :
    I = sqrtNegFiveRingOfIntegersIdealTwo := by
  let hfinite : Finite (SqrtNegFiveRingOfIntegers ⧸ I) :=
    (Ideal.absNorm_ne_zero_iff I).mp (by omega)
  let _ : Fintype (SqrtNegFiveRingOfIntegers ⧸ I) := Fintype.ofFinite _
  have hcard : Fintype.card (SqrtNegFiveRingOfIntegers ⧸ I) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
    exact hI
  let e : ZMod 2 ≃+* SqrtNegFiveRingOfIntegers ⧸ I :=
    ZMod.ringEquivOfPrime _ (by decide) hcard
  let f : SqrtNegFiveRingOfIntegers →+* ZMod 2 :=
    e.symm.toRingHom.comp (Ideal.Quotient.mk I)
  have hf : f = sqrtNegFiveRingOfIntegersModTwo :=
    ringHom_eq_sqrtNegFiveRingOfIntegersModTwo f
  have hker : RingHom.ker f = I := by
    ext x
    constructor
    · intro hx
      have hxq : Ideal.Quotient.mk I x = 0 :=
        e.symm.injective (by simpa [f] using hx)
      exact Ideal.Quotient.eq_zero_iff_mem.mp hxq
    · intro hx
      have hxq : Ideal.Quotient.mk I x = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      simp [f, hxq]
  simpa [sqrtNegFiveRingOfIntegersIdealTwo, hf] using hker.symm

/-- The distinguished norm-two ideal, packaged as a nonzero ideal for the
class-group API. -/
@[expose]
def sqrtNegFiveRingOfIntegersIdealTwoNonzero :
    ↥(nonZeroDivisors (Ideal SqrtNegFiveRingOfIntegers)) :=
  ⟨sqrtNegFiveRingOfIntegersIdealTwo,
    mem_nonZeroDivisors_iff_ne_zero.mpr (by
      intro hzero
      have habs := absNorm_sqrtNegFiveRingOfIntegersIdealTwo
      rw [hzero] at habs
      simp at habs)⟩

/-- A nonzero ideal of absolute norm at most two in the ring of integers of
`ℚ(√-5)` is either the unit ideal or the distinguished norm-two ideal. -/
theorem eq_top_or_eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_le_two
    (I : ↥(nonZeroDivisors (Ideal SqrtNegFiveRingOfIntegers)))
    (hI : Ideal.absNorm (I : Ideal SqrtNegFiveRingOfIntegers) ≤ 2) :
    (I : Ideal SqrtNegFiveRingOfIntegers) = ⊤ ∨
      (I : Ideal SqrtNegFiveRingOfIntegers) =
        sqrtNegFiveRingOfIntegersIdealTwo := by
  have hpos : 0 < Ideal.absNorm (I : Ideal SqrtNegFiveRingOfIntegers) :=
    Ideal.absNorm_pos_of_nonZeroDivisors I
  have hcases : Ideal.absNorm (I : Ideal SqrtNegFiveRingOfIntegers) = 1 ∨
      Ideal.absNorm (I : Ideal SqrtNegFiveRingOfIntegers) = 2 := by
    omega
  rcases hcases with hone | htwo
  · exact Or.inl (Ideal.absNorm_eq_one_iff.mp hone)
  · exact Or.inr
      (eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_eq_two I htwo)

/-- Every ideal class of `ℚ(√-5)` is either trivial or represented by the
distinguished norm-two ideal. -/
theorem classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo
    (C : ClassGroup SqrtNegFiveRingOfIntegers) :
    C = 1 ∨ C = ClassGroup.mk0 sqrtNegFiveRingOfIntegersIdealTwoNonzero := by
  obtain ⟨I, hclass, hnorm⟩ :=
    exists_ideal_in_class_of_absNorm_le_two C
  rcases
      eq_top_or_eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_le_two I hnorm with
    htop | htwo
  · left
    rw [← hclass]
    exact (ClassGroup.mk0_eq_one_iff I.prop).mpr
      (htop.symm ▸ top_isPrincipal)
  · right
    rw [← hclass]
    congr 1
    exact Subtype.ext htwo

/-- The class number of `ℚ(√-5)` is two. -/
theorem classNumber_sqrtNegFiveField :
    NumberField.classNumber SqrtNegFiveField = 2 := by
  rw [NumberField.classNumber, ← Nat.card_eq_fintype_card,
    Nat.card_eq_two_iff]
  refine ⟨1, ClassGroup.mk0 sqrtNegFiveRingOfIntegersIdealTwoNonzero, ?_, ?_⟩
  · intro heq
    apply not_isPrincipal_sqrtNegFiveRingOfIntegersIdealTwo
    exact (ClassGroup.mk0_eq_one_iff
      sqrtNegFiveRingOfIntegersIdealTwoNonzero.prop).mp heq.symm
  · ext C
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo C

end QuadraticAlgebra
