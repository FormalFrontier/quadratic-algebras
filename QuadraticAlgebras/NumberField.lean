/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.FractionRing
public import QuadraticAlgebras.IntegralClosureInt
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Tactic

/-!
# Number fields from integer quadratic algebras

This file connects the coordinate model `QuadraticAlgebra ℤ a b` to the
number-field API.  It also records the elementary degree, discriminant,
signature, and Minkowski-bound computations for `ℤ[√-5]`.

The separate `QuadraticAlgebras.ClassNumberNegFive` module builds on these
results to classify the ideals of norm at most two and compute the class number.

## References

* Mathlib's [number-field class-number formalization](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/NumberTheory/NumberField/ClassNumber.lean)
  by Anne Baanen, Riccardo Brasca and Xavier Roblot supplies
  `NumberField.exists_ideal_in_class_of_norm_le`. The discriminant, bound
  computation and norm-two specialization are assembled in this library.
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace QuadraticAlgebra

/-- Transport a quadratic algebra along a ring equivalence of its
coefficients. -/
@[expose]
def mapCoeffsEquiv {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) (a b : S) :
    QuadraticAlgebra S a b ≃+* QuadraticAlgebra T (e a) (e b) where
  toFun x := QuadraticAlgebra.mk (e x.re) (e x.im)
  invFun x := QuadraticAlgebra.mk (e.symm x.re) (e.symm x.im)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

/-- Transport a quadratic algebra along a ring equivalence, with the target
coefficients presented by equalities. -/
@[expose]
def mapCoeffsEquivOfEq {S T : Type*} [CommRing S] [CommRing T]
    (e : S ≃+* T) {a b : S} (a' b' : T)
    (ha : e a = a') (hb : e b = b') :
    QuadraticAlgebra S a b ≃+* QuadraticAlgebra T a' b' := by
  subst a'
  subst b'
  exact mapCoeffsEquiv e a b

set_option linter.style.haveILetI false in
/-- The fraction field of a domain integer quadratic algebra is a number
field. -/
instance numberField_fractionRing (a b : ℤ)
    [IsDomain (QuadraticAlgebra ℤ a b)] :
    NumberField (FractionRing (QuadraticAlgebra ℤ a b)) := by
  letI := FractionRing.liftAlgebra ℤ
    (FractionRing (QuadraticAlgebra ℤ a b))
  letI := FractionRing.isScalarTower_liftAlgebra ℤ
    (FractionRing (QuadraticAlgebra ℤ a b))
  let _ : Module.Finite (FractionRing ℤ)
      (FractionRing (QuadraticAlgebra ℤ a b)) :=
    Module.Finite.of_isLocalization ℤ (QuadraticAlgebra ℤ a b) ℤ⁰
  let _ : NumberField (FractionRing ℤ) :=
    NumberField.of_ringEquiv ℚ (FractionRing ℤ)
      (FractionRing.algEquiv ℤ ℚ).symm.toRingEquiv
  exact NumberField.of_module_finite (FractionRing ℤ)
    (FractionRing (QuadraticAlgebra ℤ a b))

/-- An integrally closed domain integer quadratic algebra is canonically the
ring of integers of its fraction field. -/
@[expose]
def ringOfIntegersEquiv (a b : ℤ)
    [IsDomain (QuadraticAlgebra ℤ a b)]
    [IsIntegrallyClosed (QuadraticAlgebra ℤ a b)] :
    QuadraticAlgebra ℤ a b ≃+*
      NumberField.RingOfIntegers (FractionRing (QuadraticAlgebra ℤ a b)) := by
  let _ : IsScalarTower ℤ (QuadraticAlgebra ℤ a b)
      (FractionRing (QuadraticAlgebra ℤ a b)) := inferInstance
  let _ : IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ
      (FractionRing (QuadraticAlgebra ℤ a b)) :=
    IsIntegralClosure.of_isIntegrallyClosed (QuadraticAlgebra ℤ a b) ℤ
      (FractionRing (QuadraticAlgebra ℤ a b))
  exact (NumberField.RingOfIntegers.equiv (QuadraticAlgebra ℤ a b)).symm

/-- The integer quadratic order `ℤ[√-5]`. -/
abbrev SqrtNegFiveOrder := QuadraticAlgebra ℤ (-5 : ℤ) 0

/-- The fraction field of `ℤ[√-5]`. -/
abbrev SqrtNegFiveField := FractionRing SqrtNegFiveOrder

/-- The integer order `ℤ[√-5]` is a domain, using `-5 ≡ 3 mod 4`. -/
instance : IsDomain SqrtNegFiveOrder :=
  isDomain_int_of_emod_four (by norm_num)

/-- Squarefreeness of `-5` and its remainder modulo four make `ℤ[√-5]`
integrally closed. This is a global instance for the specified order. -/
instance : IsIntegrallyClosed SqrtNegFiveOrder :=
  isIntegrallyClosed_int_of_squarefree_of_emod_four (by
    rw [Associated.rfl.neg_left.squarefree_iff]
    exact (show Prime (5 : ℤ) by norm_num).squarefree) (by norm_num)

/-- The canonical identification of `ℤ[√-5]` with the ring of integers of its
fraction field. -/
@[expose]
def sqrtNegFiveRingOfIntegersEquiv :
    SqrtNegFiveOrder ≃+* NumberField.RingOfIntegers SqrtNegFiveField :=
  ringOfIntegersEquiv (-5) 0

/-- On `ℤ[√-5]`, algebra trace agrees with quadratic-algebra trace. -/
theorem algebraTrace_eq_trace_sqrtNegFive (x : SqrtNegFiveOrder) :
    Algebra.trace ℤ SqrtNegFiveOrder x = QuadraticAlgebra.trace x := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (-5 : ℤ) 0)]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul,
    QuadraticAlgebra.trace_def]
  ring

/-- The standard basis of `ℤ[√-5]` has discriminant `-20`. -/
theorem discr_sqrtNegFiveOrder_basis :
    Algebra.discr ℤ (QuadraticAlgebra.basis (-5 : ℤ) 0) = -20 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  norm_num [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    algebraTrace_eq_trace_sqrtNegFive, QuadraticAlgebra.trace_def]

/-- The integral basis of the number field induced by the standard basis of
`ℤ[√-5]`. -/
@[expose]
def sqrtNegFiveRingOfIntegersBasis :
    Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers SqrtNegFiveField) :=
  (QuadraticAlgebra.basis (-5 : ℤ) 0).map
    sqrtNegFiveRingOfIntegersEquiv.toIntAlgEquiv.toLinearEquiv

/-- The number-field discriminant of `ℚ(√-5)` is `-20`. -/
theorem discr_sqrtNegFiveField : NumberField.discr SqrtNegFiveField = -20 := by
  rw [← NumberField.discr_eq_discr SqrtNegFiveField
    sqrtNegFiveRingOfIntegersBasis]
  change Algebra.discr ℤ
    (sqrtNegFiveRingOfIntegersEquiv.toIntAlgEquiv ∘
      QuadraticAlgebra.basis (-5 : ℤ) 0) = -20
  rw [← Algebra.discr_eq_discr_of_algEquiv
    (QuadraticAlgebra.basis (-5 : ℤ) 0)
      sqrtNegFiveRingOfIntegersEquiv.toIntAlgEquiv]
  exact discr_sqrtNegFiveOrder_basis

/-- The fraction field of `ℤ[√-5]` as the corresponding rational quadratic
algebra. -/
@[expose]
def sqrtNegFiveFieldEquivRatQuadratic :
    SqrtNegFiveField ≃ₐ[ℚ] QuadraticAlgebra ℚ (-5 : ℚ) 0 := by
  let e₀ := (fractionRingEquivBaseChange (-5 : ℤ) 0).toRingEquiv
  have h₅ : (FractionRing.algEquiv ℤ ℚ)
      (algebraMap ℤ (FractionRing ℤ) (-5 : ℤ)) = (-5 : ℚ) :=
    (FractionRing.algEquiv ℤ ℚ).commutes (-5 : ℤ)
  have h₀ : (FractionRing.algEquiv ℤ ℚ)
      (algebraMap ℤ (FractionRing ℤ) 0) = (0 : ℚ) :=
    (FractionRing.algEquiv ℤ ℚ).commutes 0
  have h₅' : (FractionRing.algEquiv ℤ ℚ).toRingEquiv
      (algebraMap ℤ (FractionRing ℤ) (-5 : ℤ)) = (-5 : ℚ) := h₅
  have h₀' : (FractionRing.algEquiv ℤ ℚ).toRingEquiv
      (algebraMap ℤ (FractionRing ℤ) 0) = (0 : ℚ) := h₀
  let e₁ := mapCoeffsEquivOfEq (FractionRing.algEquiv ℤ ℚ).toRingEquiv
    (-5 : ℚ) 0 h₅' h₀'
  exact (e₀.trans e₁).toRatAlgEquiv

/-- The degree of `ℚ(√-5)` over `ℚ` is two. -/
theorem finrank_sqrtNegFiveField : Module.finrank ℚ SqrtNegFiveField = 2 := by
  rw [LinearEquiv.finrank_eq
    sqrtNegFiveFieldEquivRatQuadratic.toLinearEquiv]
  exact QuadraticAlgebra.finrank_eq_two (-5 : ℚ) 0

/-- The field `ℚ(√-5)` is totally complex: a real embedding would send a square
to `-5`, contradicting nonnegativity of real squares. -/
instance : NumberField.IsTotallyComplex SqrtNegFiveField where
  isComplex w := by
    rw [NumberField.InfinitePlace.isComplex_iff]
    intro hreal
    let ψ := NumberField.InfinitePlace.embedding_of_isReal
      (NumberField.InfinitePlace.isReal_iff.mpr hreal)
    let α : SqrtNegFiveField := sqrtNegFiveFieldEquivRatQuadratic.symm
      (omega : QuadraticAlgebra ℚ (-5 : ℚ) 0)
    have hα : α * α = (-5 : SqrtNegFiveField) := by
      apply sqrtNegFiveFieldEquivRatQuadratic.injective
      simp [α, ← map_mul, omega_mul_omega_eq_algebraMap]
    have hψ := congr_arg ψ hα
    simp only [map_mul, map_neg, map_ofNat] at hψ
    nlinarith [sq_nonneg (ψ α)]

/-- The number field `ℚ(√-5)` has exactly one complex place. -/
theorem nrComplexPlaces_sqrtNegFiveField :
    NumberField.InfinitePlace.nrComplexPlaces SqrtNegFiveField = 1 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
    SqrtNegFiveField
  rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero,
    finrank_sqrtNegFiveField] at h
  omega

/-- The explicit Minkowski bound for ideal-class representatives in
`ℚ(√-5)` is strictly less than three. -/
theorem classGroup_minkowskiBound_sqrtNegFiveField_lt_three :
    (4 / Real.pi) ^
        NumberField.InfinitePlace.nrComplexPlaces SqrtNegFiveField *
      ((Module.finrank ℚ SqrtNegFiveField).factorial /
          (Module.finrank ℚ SqrtNegFiveField : ℝ) ^
            Module.finrank ℚ SqrtNegFiveField *
        Real.sqrt |(NumberField.discr SqrtNegFiveField : ℝ)|) < 3 := by
  rw [nrComplexPlaces_sqrtNegFiveField, finrank_sqrtNegFiveField,
    discr_sqrtNegFiveField]
  norm_num [abs_of_nonneg]
  have hsqrt : Real.sqrt 20 < (9 / 2 : ℝ) := by
    have hsqrt_nonneg := Real.sqrt_nonneg 20
    have hsqrt_sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 20)
    nlinarith
  rw [show 4 / Real.pi * (1 / 2 * Real.sqrt 20) =
    (2 * Real.sqrt 20) / Real.pi by ring]
  rw [div_lt_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

/-- Every ideal class of `ℚ(√-5)` has an integral representative of absolute
norm at most two. This applies Mathlib's prior formalization
`NumberField.exists_ideal_in_class_of_norm_le` (Anne Baanen, Riccardo Brasca
and Xavier Roblot) to the discriminant and Minkowski bound computed here. -/
theorem exists_ideal_in_class_of_absNorm_le_two
    (C : ClassGroup (NumberField.RingOfIntegers SqrtNegFiveField)) :
    ∃ I,
      ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal
        (NumberField.RingOfIntegers SqrtNegFiveField)) ≤ 2 := by
  obtain ⟨I, hI, hnorm⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  refine ⟨I, hI, ?_⟩
  have hnorm_real :
      (Ideal.absNorm (I : Ideal
        (NumberField.RingOfIntegers SqrtNegFiveField)) : ℝ) < 3 :=
    lt_of_le_of_lt hnorm
      classGroup_minkowskiBound_sqrtNegFiveField_lt_three
  have hnorm_nat : Ideal.absNorm (I : Ideal
      (NumberField.RingOfIntegers SqrtNegFiveField)) < 3 := by
    exact_mod_cast hnorm_real
  omega

end QuadraticAlgebra
