/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Tactic

/-!
# The arithmetic quadratic algebra of `√-5` is not a UFD

This file proves that `QuadraticAlgebra ℤ (-5) 0` is not a unique
factorization monoid. The embedded integer `2` is irreducible because the norm
form `x² + 5y²` does not represent `2`, but it is not prime because
`(1 + ω) * (1 - ω) = 6` while `2` divides neither factor.
-/

public section

set_option warningAsError true

namespace QuadraticAlgebra

/-- In the integer quadratic algebra with `ω² = -5`, the norm is
`x.re² + 5 * x.im²`. -/
theorem norm_int_negFive_eq (x : QuadraticAlgebra ℤ (-5 : ℤ) 0) :
    norm x = x.re ^ 2 + 5 * x.im ^ 2 := by
  rw [norm_def]
  ring

private theorem norm_int_negFive_nonneg (x : QuadraticAlgebra ℤ (-5 : ℤ) 0) :
    0 ≤ norm x := by
  rw [norm_int_negFive_eq]
  positivity

/-- An element of `QuadraticAlgebra ℤ (-5) 0` is a unit exactly when its norm
is `1`. -/
theorem isUnit_iff_norm_eq_one_int_negFive {x : QuadraticAlgebra ℤ (-5 : ℤ) 0} :
    IsUnit x ↔ norm x = 1 := by
  rw [isUnit_iff_norm_isUnit]
  constructor
  · intro hx
    rw [Int.isUnit_iff] at hx
    rcases hx with h | h
    · exact h
    · have hnonneg := norm_int_negFive_nonneg x
      omega
  · intro h
    rw [h]
    exact isUnit_one

private theorem norm_int_negFive_ne_two (x : QuadraticAlgebra ℤ (-5 : ℤ) 0) :
    norm x ≠ 2 := by
  rw [norm_int_negFive_eq]
  intro h
  have him : x.im = 0 := by
    nlinarith [sq_nonneg x.re, sq_nonneg x.im]
  rw [him] at h
  norm_num at h
  have hlo : -2 < x.re := by nlinarith [sq_nonneg x.re]
  have hhi : x.re < 2 := by nlinarith [sq_nonneg x.re]
  interval_cases x.re <;> norm_num at h

/-- The embedded integer `2` is irreducible in
`QuadraticAlgebra ℤ (-5) 0`. -/
theorem irreducible_two_int_negFive :
    Irreducible (2 : QuadraticAlgebra ℤ (-5 : ℤ) 0) := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_norm_eq_one_int_negFive]
    norm_num [norm_def]
  · intro a b hab
    by_contra h
    simp only [not_or] at h
    have hnorm_two : norm (2 : QuadraticAlgebra ℤ (-5 : ℤ) 0) = 4 := by
      norm_num [norm_def]
    have hnorm := congr_arg norm hab
    rw [map_mul, hnorm_two] at hnorm
    have hna0 : norm a ≠ 0 := by
      intro ha
      rw [ha, zero_mul] at hnorm
      norm_num at hnorm
    have hnb0 : norm b ≠ 0 := by
      intro hb
      rw [hb, mul_zero] at hnorm
      norm_num at hnorm
    have hna1 : norm a ≠ 1 := by
      intro ha
      exact h.1 (isUnit_iff_norm_eq_one_int_negFive.mpr ha)
    have hnb1 : norm b ≠ 1 := by
      intro hb
      exact h.2 (isUnit_iff_norm_eq_one_int_negFive.mpr hb)
    have hna2 : 2 ≤ norm a := by
      have := norm_int_negFive_nonneg a
      omega
    have hnb2 : 2 ≤ norm b := by
      have := norm_int_negFive_nonneg b
      omega
    have : norm a = 2 := by nlinarith
    exact norm_int_negFive_ne_two a this

private theorem one_add_omega_mul_one_sub_omega :
    ((1 : QuadraticAlgebra ℤ (-5 : ℤ) 0) + omega) * (1 - omega) = 6 := by
  ext <;> norm_num

private theorem two_not_dvd_one_add_omega :
    ¬(2 : QuadraticAlgebra ℤ (-5 : ℤ) 0) ∣ 1 + omega := by
  rintro ⟨x, hx⟩
  have him := congr_arg im hx
  norm_num at him
  omega

private theorem two_not_dvd_one_sub_omega :
    ¬(2 : QuadraticAlgebra ℤ (-5 : ℤ) 0) ∣ 1 - omega := by
  rintro ⟨x, hx⟩
  have him := congr_arg im hx
  norm_num at him
  omega

/-- The embedded integer `2` is not prime in
`QuadraticAlgebra ℤ (-5) 0`. -/
theorem not_prime_two_int_negFive :
    ¬Prime (2 : QuadraticAlgebra ℤ (-5 : ℤ) 0) := by
  intro hp
  have hdiv : (2 : QuadraticAlgebra ℤ (-5 : ℤ) 0) ∣
      ((1 : QuadraticAlgebra ℤ (-5 : ℤ) 0) + omega) * (1 - omega) := by
    rw [one_add_omega_mul_one_sub_omega]
    use 3
    norm_num
  rcases (hp.dvd_mul.mp hdiv) with h | h
  · exact two_not_dvd_one_add_omega h
  · exact two_not_dvd_one_sub_omega h

/-- The integer quadratic algebra `QuadraticAlgebra ℤ (-5) 0` is not a unique
factorization monoid. -/
theorem not_uniqueFactorizationMonoid_int_negFive :
    ¬UniqueFactorizationMonoid (QuadraticAlgebra ℤ (-5 : ℤ) 0) := by
  intro h
  let _ : UniqueFactorizationMonoid (QuadraticAlgebra ℤ (-5 : ℤ) 0) := h
  exact not_prime_two_int_negFive
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp irreducible_two_int_negFive)

end QuadraticAlgebra
