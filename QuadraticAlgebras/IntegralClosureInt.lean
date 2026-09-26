/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.IntegralClosure
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Integral closure of quadratic algebras over the integers

The quadratic algebra `ℤ[ω]` with `ω² = f` is a domain and is integrally
closed when `f` is squarefree and congruent to `2` or `3` modulo `4`. The proof
descends twice each coordinate from the total fraction ring using the trace,
norm, and squarefree denominator descent. The congruence condition then forces
both descended integer coordinates to be even.
-/

public section

set_option warningAsError true

noncomputable section

namespace QuadraticAlgebra

open Polynomial

/-- If an integer is congruent to `2` or `3` modulo `4`, then adjoining a
square root of it to the integers gives a domain. -/
theorem isDomain_int_of_emod_four {f : ℤ}
    (hmod : f % 4 = 2 ∨ f % 4 = 3) :
    IsDomain (QuadraticAlgebra ℤ f 0) := by
  have hp_monic : (definingPolynomial f 0).Monic :=
    definingPolynomial_monic f 0
  have hp_irred : Irreducible (definingPolynomial f 0) := by
    rw [hp_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · rw [Multiset.eq_zero_iff_forall_notMem]
      intro r hr
      have hroot := (Polynomial.mem_roots hp_monic.ne_zero).mp hr
      have hsquare : r ^ 2 = f := by
        exact sub_eq_zero.mp (by
          simpa [Polynomial.IsRoot, definingPolynomial] using hroot)
      have hsquare_mod : f % 4 = r % 2 := by
        rw [← hsquare, Int.sq_emod_four]
      rcases Int.emod_two_eq_zero_or_one r with hr | hr <;>
        rcases hmod with hf | hf <;>
        omega
    · rw [show definingPolynomial f 0 = X ^ 2 - C f by
        simp [definingPolynomial], Polynomial.natDegree_X_pow_sub_C]
    · rw [show definingPolynomial f 0 = X ^ 2 - C f by
        simp [definingPolynomial], Polynomial.natDegree_X_pow_sub_C]
      norm_num
  exact @Function.Injective.isDomain
    (AdjoinRoot (definingPolynomial f 0)) (QuadraticAlgebra ℤ f 0)
    inferInstance (AdjoinRoot.isDomain_of_prime hp_irred.prime) inferInstance
    (QuadraticAlgebra ℤ f 0 ≃ₐ[ℤ] AdjoinRoot (definingPolynomial f 0))
    inferInstance inferInstance (equivAdjoinRoot f 0)
    (equivAdjoinRoot f 0).injective

/-- If `f` is `2` or `3` modulo `4` and `r² - f s²` is divisible by `4`, then
both `r` and `s` are even. -/
private theorem two_dvd_coordinates_of_emod_four {f r s n : ℤ}
    (hf : f % 4 = 2 ∨ f % 4 = 3)
    (h : r ^ 2 - f * s ^ 2 = 4 * n) :
    2 ∣ r ∧ 2 ∣ s := by
  have heq : (r ^ 2 - f * s ^ 2) % 4 = 0 := by rw [h]; simp
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four,
    Int.sq_emod_four] at heq
  simp only [Int.dvd_iff_emod_eq_zero]
  rcases Int.emod_two_eq_zero_or_one r with hr | hr <;>
    rcases Int.emod_two_eq_zero_or_one s with hs | hs <;>
    rcases hf with hf | hf <;>
    simp only [hr, hs, hf] at heq ⊢
  all_goals norm_num at heq
  all_goals norm_num

private theorem isIntegrallyClosed_int_of_squarefree_of_emod_four_of_isDomain
    {f : ℤ} (hf : Squarefree f) (hmod : f % 4 = 2 ∨ f % 4 = 3)
    [IsDomain (QuadraticAlgebra ℤ f 0)] :
    IsIntegrallyClosed (QuadraticAlgebra ℤ f 0) := by
  rw [isIntegrallyClosed_iff (FractionRing (QuadraticAlgebra ℤ f 0))]
  intro x hx
  let e := fractionRingEquivBaseChange f 0
  let y := e x
  have hy : IsIntegral ℤ y := by
    exact (isIntegral_trans x hx).map e.toAlgHom
  obtain ⟨t, ht⟩ := isInteger_trace_of_isIntegral hy
  obtain ⟨n, hn⟩ := isInteger_norm_of_isIntegral hy
  have him_sq : IsLocalization.IsInteger ℤ
      ((2 * y.im) ^ 2 * algebraMap ℤ (FractionRing ℤ) f) := by
    refine ⟨t ^ 2 - 4 * n, ?_⟩
    rw [map_sub, map_pow, map_mul, ht, hn]
    simp only [trace_def, norm_def, map_zero, zero_mul, add_zero]
    norm_num only [map_ofNat]
    ring
  obtain ⟨u, hu⟩ :=
    IsFractionRing.isInteger_of_sq_mul_squarefree hf him_sq
  have hparity : t ^ 2 - f * u ^ 2 = 4 * n := by
    apply IsFractionRing.injective ℤ (FractionRing ℤ)
    rw [map_sub, map_pow, map_mul, map_pow, map_mul, hu, hn]
    rw [ht]
    simp only [trace_def, norm_def, map_zero, zero_mul, add_zero]
    norm_num only [map_ofNat]
    ring
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ :=
    two_dvd_coordinates_of_emod_four hmod hparity
  have htwo : (2 : FractionRing ℤ) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using
      (IsFractionRing.injective ℤ (FractionRing ℤ)).ne
        (by norm_num : (2 : ℤ) ≠ 0)
  have hre : algebraMap ℤ (FractionRing ℤ) r = y.re := by
    rw [hr, map_mul] at ht
    simp only [trace_def, map_zero, zero_mul, add_zero] at ht
    apply mul_left_cancel₀ htwo
    simpa only [map_ofNat] using ht
  have him : algebraMap ℤ (FractionRing ℤ) s = y.im := by
    rw [hs, map_mul] at hu
    apply mul_left_cancel₀ htwo
    simpa only [map_ofNat] using hu
  refine ⟨QuadraticAlgebra.mk r s, ?_⟩
  apply e.injective
  rw [fractionRingEquivBaseChange_algebraMap]
  ext
  · exact hre
  · exact him

/-- A quadratic algebra over the integers with squarefree radicand is
integrally closed when the radicand is congruent to `2` or `3` modulo `4`. -/
theorem isIntegrallyClosed_int_of_squarefree_of_emod_four
    {f : ℤ} (hf : Squarefree f) (hmod : f % 4 = 2 ∨ f % 4 = 3) :
    IsIntegrallyClosed (QuadraticAlgebra ℤ f 0) :=
  @isIntegrallyClosed_int_of_squarefree_of_emod_four_of_isDomain f hf hmod
    (isDomain_int_of_emod_four hmod)

end QuadraticAlgebra
