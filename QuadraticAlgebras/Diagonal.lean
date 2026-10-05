/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Diagonal multivariate quadratics

This file defines the diagonal quadratic `∑ i, c i • X i ^ 2` attached to a
finitely supported coefficient family.  It proves reusable coefficient,
homogeneity, irreducibility, and squarefreeness results over fields of
characteristic different from two.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.I(b), motivates a diagonal prerequisite, while
  Exercise 5.4.N motivates the binary diagonal case. These polynomial results
  alone do not establish the hypersurface-normality exercise.
* Mathlib's [multivariate quadratic results](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/MvPolynomial/IrreducibleQuadratic.lean)
  provide the polynomial infrastructure used here.
-/

public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

variable {ι R : Type*} [CommRing R]

/-- The diagonal quadratic polynomial `∑ i, c i • X i ^ 2`. -/
@[expose]
noncomputable def sumSMulXSq :
    (ι →₀ R) →ₗ[R] MvPolynomial ι R :=
  Finsupp.linearCombination R fun i ↦ X i ^ 2

/-- Evaluate the linear construction as the finite sum of its diagonal terms. -/
theorem sumSMulXSq_apply (c : ι →₀ R) :
    sumSMulXSq c = c.sum fun i a ↦ a • X i ^ 2 := by
  simp [sumSMulXSq, Finsupp.linearCombination_apply]

/-- The coefficient of the monomial `X i ^ 2` is the given coefficient `c i`. -/
theorem coeff_sumSMulXSq (c : ι →₀ R) (i : ι) :
    (sumSMulXSq c).coeff (Finsupp.single i 2) = c i := by
  classical
  rw [sumSMulXSq_apply, Finsupp.sum, coeff_sum]
  rw [Finset.sum_eq_single i]
  · simp [X_pow_eq_monomial]
  · intro j hj hji
    simp [X_pow_eq_monomial, Finsupp.single_left_inj, hji]
  · intro hi
    rw [Finsupp.notMem_support_iff] at hi
    simp [hi]

/-- The derivative in variable `i` is `2 * c i * X i`, over any commutative
ring, including characteristic two. -/
theorem pderiv_sumSMulXSq (c : ι →₀ R) (i : ι) :
    pderiv i (sumSMulXSq c) = C (2 * c i) * X i := by
  classical
  rw [sumSMulXSq_apply, Finsupp.sum, map_sum]
  simp_rw [(pderiv i).map_smul, pderiv_pow]
  rw [Finset.sum_eq_single i]
  · simp only [smul_eq_C_mul, Nat.reduceSub, pow_one, pderiv_X_self, mul_one]
    have htwo : (↑(2 : ℕ) : MvPolynomial ι R) = C (2 : R) :=
      (map_natCast (C : R →+* MvPolynomial ι R) 2).symm
    rw [htwo]
    rw [← mul_assoc, ← C_mul, mul_comm (c i) 2]
  · intro j hj hji
    simp [hji]
  · intro hi
    rw [Finsupp.notMem_support_iff] at hi
    simp [hi]

/-- A diagonal quadratic is homogeneous of degree two, also when all its
coefficients vanish; no field or nonzero-coefficient hypothesis is required. -/
theorem isHomogeneous_sumSMulXSq (c : ι →₀ R) :
    (sumSMulXSq c).IsHomogeneous 2 := by
  rw [sumSMulXSq_apply]
  rw [Finsupp.sum]
  apply IsHomogeneous.sum
  intro i hi
  simpa [smul_eq_C_mul] using (isHomogeneous_X_pow i 2).C_mul (c i)

section Field

variable {k : Type*} [Field k]

private theorem isHomogeneous_one_of_totalDegree_eq_one_of_coeff_zero
    {f : MvPolynomial ι k} (hdeg : f.totalDegree = 1) (hzero : f.coeff 0 = 0) :
    f.IsHomogeneous 1 := by
  have h := sum_homogeneousComponent f
  rw [hdeg] at h
  norm_num [Finset.sum_range_succ, homogeneousComponent_zero, hzero] at h
  rw [← h]
  exact homogeneousComponent_isHomogeneous (φ := f) (n := 1)

private theorem pderiv_eq_C_coeff_of_isHomogeneous_one
    {f : MvPolynomial ι k} (hf : f.IsHomogeneous 1) (i : ι) :
    pderiv i f = C (f.coeff (Finsupp.single i 1)) := by
  have h := homogeneousComponent_eq_self (hf.pderiv (i := i))
  rw [homogeneousComponent_zero] at h
  rw [← h]
  congr 1
  simp [coeff_pderiv]

private theorem second_pderiv_mul_of_isHomogeneous_one
    {a b : MvPolynomial ι k} (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1)
    (i j : ι) :
    pderiv i (pderiv j (a * b)) =
      C (a.coeff (Finsupp.single j 1) * b.coeff (Finsupp.single i 1) +
        a.coeff (Finsupp.single i 1) * b.coeff (Finsupp.single j 1)) := by
  rw [pderiv_mul, map_add, pderiv_mul, pderiv_mul,
    pderiv_eq_C_coeff_of_isHomogeneous_one ha,
    pderiv_eq_C_coeff_of_isHomogeneous_one hb,
    pderiv_eq_C_coeff_of_isHomogeneous_one ha,
    pderiv_eq_C_coeff_of_isHomogeneous_one hb,
    pderiv_C, pderiv_C]
  simp only [zero_mul, zero_add, mul_zero, add_zero, ← C_mul, ← C_add]

private theorem factors_isHomogeneous_one
    {q a b : MvPolynomial ι k} (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (hab : a * b = q) (ha : ¬IsUnit a) (hb : ¬IsUnit b) :
    a.IsHomogeneous 1 ∧ b.IsHomogeneous 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hab
    exact hq0 hab.symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hab
    exact hq0 hab.symm
  have hdeg : a.totalDegree + b.totalDegree = 2 := by
    rw [← totalDegree_mul_of_isDomain ha0 hb0, hab, hq.totalDegree hq0]
  have hda0 : a.totalDegree ≠ 0 := by
    intro h
    have heq := totalDegree_eq_zero_iff_eq_C.mp h
    apply ha
    rw [isUnit_iff_totalDegree_of_isReduced]
    refine ⟨isUnit_iff_ne_zero.mpr ?_, h⟩
    intro hac
    apply ha0
    rw [heq, hac]
    simp
  have hdb0 : b.totalDegree ≠ 0 := by
    intro h
    have heq := totalDegree_eq_zero_iff_eq_C.mp h
    apply hb
    rw [isUnit_iff_totalDegree_of_isReduced]
    refine ⟨isUnit_iff_ne_zero.mpr ?_, h⟩
    intro hbc
    apply hb0
    rw [heq, hbc]
    simp
  have hda : a.totalDegree = 1 := by omega
  have hdb : b.totalDegree = 1 := by omega
  have hqconst : q.coeff 0 = 0 := hq.coeff_eq_zero (by norm_num)
  have hconst : a.coeff 0 * b.coeff 0 = 0 := by
    have h := congrArg (constantCoeff : MvPolynomial ι k →+* k) hab
    simpa only [map_mul, constantCoeff_eq, hqconst] using h
  rcases mul_eq_zero.mp hconst with ha_const | hb_const
  · have ha_hom :=
      isHomogeneous_one_of_totalDegree_eq_one_of_coeff_zero hda ha_const
    have hb_decomp :
        C (b.coeff 0) + homogeneousComponent 1 b = b := by
      have h := sum_homogeneousComponent b
      rw [hdb] at h
      norm_num [Finset.sum_range_succ, homogeneousComponent_zero] at h
      exact h
    have heq :
        a * C (b.coeff 0) + a * homogeneousComponent 1 b = q := by
      rw [← mul_add, hb_decomp, hab]
    have hcomp := congrArg (homogeneousComponent 1) heq
    have haC : (a * C (b.coeff 0)).IsHomogeneous 1 := by
      simpa using ha_hom.mul (isHomogeneous_C ι (b.coeff 0))
    have haB : (a * homogeneousComponent 1 b).IsHomogeneous 2 := by
      simpa using ha_hom.mul (homogeneousComponent_isHomogeneous (φ := b) (n := 1))
    rw [map_add, homogeneousComponent_of_mem haC,
      homogeneousComponent_of_mem haB, homogeneousComponent_of_mem hq] at hcomp
    norm_num at hcomp
    have hb_const : b.coeff 0 = 0 := by
      exact hcomp.resolve_left ha0
    exact ⟨ha_hom,
      isHomogeneous_one_of_totalDegree_eq_one_of_coeff_zero hdb hb_const⟩
  · have hb_hom :=
      isHomogeneous_one_of_totalDegree_eq_one_of_coeff_zero hdb hb_const
    have ha_decomp :
        C (a.coeff 0) + homogeneousComponent 1 a = a := by
      have h := sum_homogeneousComponent a
      rw [hda] at h
      norm_num [Finset.sum_range_succ, homogeneousComponent_zero] at h
      exact h
    have heq :
        C (a.coeff 0) * b + homogeneousComponent 1 a * b = q := by
      rw [← add_mul, ha_decomp, hab]
    have hcomp := congrArg (homogeneousComponent 1) heq
    have hCb : (C (a.coeff 0) * b).IsHomogeneous 1 := by
      simpa using (isHomogeneous_C ι (a.coeff 0)).mul hb_hom
    have hAb : (homogeneousComponent 1 a * b).IsHomogeneous 2 := by
      simpa using (homogeneousComponent_isHomogeneous (φ := a) (n := 1)).mul hb_hom
    rw [map_add, homogeneousComponent_of_mem hCb,
      homogeneousComponent_of_mem hAb, homogeneousComponent_of_mem hq] at hcomp
    norm_num at hcomp
    have ha_const : a.coeff 0 = 0 := by
      exact hcomp.resolve_right hb0
    exact ⟨isHomogeneous_one_of_totalDegree_eq_one_of_coeff_zero hda ha_const,
      hb_hom⟩

/-- A diagonal quadratic over a field of characteristic different from two is
irreducible as soon as at least three coefficients are nonzero. This reusable
prerequisite is motivated by Vakil, *The Rising Sea*, Exercise 5.4.I(b), not
a proof of the hypersurface-normality exercise. -/
theorem irreducible_sumSMulXSq [NeZero (2 : k)]
    (c : ι →₀ k) (hc : 3 ≤ c.support.card) :
    Irreducible (sumSMulXSq c) := by
  classical
  have hnonempty : c.support.Nonempty := Finset.card_pos.mp (by omega)
  have hq0 : sumSMulXSq c ≠ 0 := by
    obtain ⟨i, hi⟩ := hnonempty
    intro h
    have hcoeff := congrArg (fun p : MvPolynomial ι k ↦
      p.coeff (Finsupp.single i 2)) h
    rw [coeff_sumSMulXSq] at hcoeff
    exact (Finsupp.mem_support_iff.mp hi) (by simpa using hcoeff)
  have hqhom := isHomogeneous_sumSMulXSq c
  refine ⟨?_, ?_⟩
  · intro hu
    have hdeg0 := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have hdeg2 := hqhom.totalDegree hq0
    omega
  · intro a b hab
    by_cases ha : IsUnit a
    · exact .inl ha
    by_cases hb : IsUnit b
    · exact .inr hb
    exfalso
    obtain ⟨ha_hom, hb_hom⟩ :=
      factors_isHomogeneous_one hqhom hq0 hab.symm ha hb
    obtain ⟨i, hi⟩ := hnonempty
    have hnontrivial : c.support.Nontrivial := Finset.one_lt_card.mp (by omega)
    obtain ⟨j, hj, hji⟩ := hnontrivial.exists_ne i
    have hexists : ∃ l ∈ c.support, l ≠ i ∧ l ≠ j := by
      by_contra h
      have hsubset : c.support ⊆ {i, j} := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hxij
        have hxi : x ≠ i := fun hxi ↦ hxij (.inl hxi)
        have hxj : x ≠ j := fun hxj ↦ hxij (.inr hxj)
        exact h ⟨x, hx, hxi, hxj⟩
      have := Finset.card_le_card hsubset
      have hcard : ({i, j} : Finset ι).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hji.symm)]
        simp
      rw [hcard] at this
      omega
    obtain ⟨l, hl, hli, hlj⟩ := hexists
    have hsecond (x y : ι) :
        C (a.coeff (Finsupp.single y 1) * b.coeff (Finsupp.single x 1) +
          a.coeff (Finsupp.single x 1) * b.coeff (Finsupp.single y 1)) =
          pderiv x (C (2 * c y) * X y) := by
      have h := congrArg (fun p : MvPolynomial ι k ↦ pderiv x (pderiv y p)) hab.symm
      rw [second_pderiv_mul_of_isHomogeneous_one ha_hom hb_hom,
        pderiv_sumSMulXSq] at h
      exact h
    have hdiag (x : ι) :
        a.coeff (Finsupp.single x 1) * b.coeff (Finsupp.single x 1) = c x := by
      have h := hsecond x x
      rw [pderiv_C_mul, pderiv_X_self, mul_one] at h
      have h' := (C_injective ι k) h
      apply mul_left_cancel₀ two_ne_zero
      calc
        2 * (a.coeff (Finsupp.single x 1) * b.coeff (Finsupp.single x 1)) =
            a.coeff (Finsupp.single x 1) * b.coeff (Finsupp.single x 1) +
              a.coeff (Finsupp.single x 1) * b.coeff (Finsupp.single x 1) := by ring
        _ = 2 * c x := by simpa [two_mul] using h'
    have hmixed (x y : ι) (hxy : x ≠ y) :
        a.coeff (Finsupp.single y 1) * b.coeff (Finsupp.single x 1) +
          a.coeff (Finsupp.single x 1) * b.coeff (Finsupp.single y 1) = 0 := by
      have h := hsecond x y
      rw [pderiv_C_mul, pderiv_X_of_ne hxy.symm, mul_zero] at h
      exact C_eq_zero.mp h
    have hi0 : c i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hj0 : c j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have hl0 : c l ≠ 0 := Finsupp.mem_support_iff.mp hl
    have hai : a.coeff (Finsupp.single i 1) ≠ 0 := by
      intro h
      apply hi0
      rw [← hdiag i, h, zero_mul]
    have haj : a.coeff (Finsupp.single j 1) ≠ 0 := by
      intro h
      apply hj0
      rw [← hdiag j, h, zero_mul]
    have hal : a.coeff (Finsupp.single l 1) ≠ 0 := by
      intro h
      apply hl0
      rw [← hdiag l, h, zero_mul]
    have hbi : b.coeff (Finsupp.single i 1) ≠ 0 := by
      intro h
      apply hi0
      rw [← hdiag i, h, mul_zero]
    have hbj : b.coeff (Finsupp.single j 1) ≠ 0 := by
      intro h
      apply hj0
      rw [← hdiag j, h, mul_zero]
    have hbl : b.coeff (Finsupp.single l 1) ≠ 0 := by
      intro h
      apply hl0
      rw [← hdiag l, h, mul_zero]
    have hij := hmixed i j hji.symm
    have hil := hmixed i l hli.symm
    have hjl := hmixed j l hlj.symm
    have hij' :
        a.coeff (Finsupp.single i 1) / b.coeff (Finsupp.single i 1) +
          a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1) = 0 := by
      field_simp [hbi, hbj]
      simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hij
    have hil' :
        a.coeff (Finsupp.single i 1) / b.coeff (Finsupp.single i 1) +
          a.coeff (Finsupp.single l 1) / b.coeff (Finsupp.single l 1) = 0 := by
      field_simp [hbi, hbl]
      simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hil
    have hjl' :
        a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1) +
          a.coeff (Finsupp.single l 1) / b.coeff (Finsupp.single l 1) = 0 := by
      field_simp [hbj, hbl]
      simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hjl
    have hrjl :
        a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1) =
          a.coeff (Finsupp.single l 1) / b.coeff (Finsupp.single l 1) := by
      linear_combination hij' - hil'
    have htwo :
        2 * (a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1)) = 0 := by
      calc
        2 * (a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1)) =
            a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1) +
              a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1) := by ring
        _ = a.coeff (Finsupp.single j 1) / b.coeff (Finsupp.single j 1) +
              a.coeff (Finsupp.single l 1) / b.coeff (Finsupp.single l 1) := by rw [hrjl]
        _ = 0 := hjl'
    exact (div_ne_zero haj hbj) ((mul_eq_zero.mp htwo).resolve_left two_ne_zero)

/-- A binary diagonal quadratic `a * X i ^ 2 + b * X j ^ 2` over a field of
characteristic different from two is irreducible when `i ≠ j`, `a` is
nonzero, and `-b / a` is not a square. (The last condition already forces
`b` to be nonzero.) The binary case is motivated by Vakil, *The Rising Sea*,
Exercise 5.4.N. -/
theorem irreducible_C_mul_X_sq_add_C_mul_X_sq_of_not_isSquare [NeZero (2 : k)]
    {i j : ι} (hij : i ≠ j) {a b : k} (ha0 : a ≠ 0)
    (hnsq : ¬ IsSquare (-b / a)) :
    Irreducible (C a * X i ^ 2 + C b * X j ^ 2) := by
  classical
  let c : ι →₀ k := Finsupp.single i a + Finsupp.single j b
  have hc : sumSMulXSq c = C a * X i ^ 2 + C b * X j ^ 2 := by
    rw [show c = Finsupp.single i a + Finsupp.single j b by rfl, map_add]
    simp [sumSMulXSq, smul_eq_C_mul]
  rw [← hc]
  let q : MvPolynomial ι k := sumSMulXSq c
  have hci : c i = a := by simp [c, hij]
  have hcj : c j = b := by simp [c, hij]
  have hqhom : q.IsHomogeneous 2 := isHomogeneous_sumSMulXSq c
  have hq0 : q ≠ 0 := by
    intro hq
    have hcoeff := congrArg (fun p : MvPolynomial ι k ↦
      p.coeff (Finsupp.single i 2)) hq
    rw [coeff_sumSMulXSq] at hcoeff
    exact ha0 (by simpa [hci] using hcoeff)
  change Irreducible q
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdeg0 := (isUnit_iff_totalDegree_of_isReduced.mp hunit).2
    have hdeg2 := hqhom.totalDegree hq0
    omega
  · intro u v huv
    by_cases hu : IsUnit u
    · exact .inl hu
    by_cases hv : IsUnit v
    · exact .inr hv
    exfalso
    obtain ⟨hu_hom, hv_hom⟩ :=
      factors_isHomogeneous_one hqhom hq0 huv.symm hu hv
    let ui := u.coeff (Finsupp.single i 1)
    let uj := u.coeff (Finsupp.single j 1)
    let vi := v.coeff (Finsupp.single i 1)
    let vj := v.coeff (Finsupp.single j 1)
    have hsecond (x y : ι) :
        C (u.coeff (Finsupp.single y 1) * v.coeff (Finsupp.single x 1) +
          u.coeff (Finsupp.single x 1) * v.coeff (Finsupp.single y 1)) =
          pderiv x (C (2 * c y) * X y) := by
      have h := congrArg (fun p : MvPolynomial ι k ↦ pderiv x (pderiv y p)) huv.symm
      change pderiv x (pderiv y (u * v)) =
        pderiv x (pderiv y (sumSMulXSq c)) at h
      rw [second_pderiv_mul_of_isHomogeneous_one hu_hom hv_hom,
        pderiv_sumSMulXSq] at h
      exact h
    have hii : ui * vi = a := by
      have h := hsecond i i
      rw [pderiv_C_mul, pderiv_X_self, mul_one] at h
      have h' := (C_injective ι k) h
      apply mul_left_cancel₀ two_ne_zero
      calc
        2 * (ui * vi) = ui * vi + ui * vi := by ring
        _ = 2 * c i := by simpa [ui, vi, two_mul] using h'
        _ = 2 * a := by rw [hci]
    have hjj : uj * vj = b := by
      have h := hsecond j j
      rw [pderiv_C_mul, pderiv_X_self, mul_one] at h
      have h' := (C_injective ι k) h
      apply mul_left_cancel₀ two_ne_zero
      calc
        2 * (uj * vj) = uj * vj + uj * vj := by ring
        _ = 2 * c j := by simpa [uj, vj, two_mul] using h'
        _ = 2 * b := by rw [hcj]
    have hij_coeff : uj * vi + ui * vj = 0 := by
      have h := hsecond i j
      rw [pderiv_C_mul, pderiv_X_of_ne hij.symm, mul_zero] at h
      exact C_eq_zero.mp (by simpa [ui, uj, vi, vj] using h)
    have hui : ui ≠ 0 := fun h ↦ ha0 (by simpa [h] using hii.symm)
    have hvi : vi ≠ 0 := fun h ↦ ha0 (by simpa [h] using hii.symm)
    apply hnsq
    refine ⟨uj / ui, ?_⟩
    rw [← hii, ← hjj]
    field_simp [hui, hvi]
    linear_combination -uj * hij_coeff

/-- A diagonal quadratic over a field of characteristic different from two is
squarefree as soon as at least two coefficients are nonzero. -/
theorem squarefree_sumSMulXSq [NeZero (2 : k)]
    (c : ι →₀ k) (hc : c.support.Nontrivial) :
    Squarefree (sumSMulXSq c) := by
  classical
  have hq : sumSMulXSq c ≠ 0 := by
    obtain ⟨i, hi⟩ := hc.nonempty
    intro h
    have hcoeff := congrArg (fun p : MvPolynomial ι k ↦
      p.coeff (Finsupp.single i 2)) h
    rw [coeff_sumSMulXSq] at hcoeff
    exact (Finsupp.mem_support_iff.mp hi) (by simpa using hcoeff)
  rw [squarefree_iff_no_irreducibles hq]
  intro p hp hp_sq
  obtain ⟨i, hi⟩ := hc.nonempty
  obtain ⟨j, hj, hji⟩ := hc.exists_ne i
  have hp_pderiv (x : ι) : p ∣ pderiv x (sumSMulXSq c) := by
    obtain ⟨r, hr⟩ := hp_sq
    refine ⟨pderiv x p * r + pderiv x p * r + p * pderiv x r, ?_⟩
    rw [hr, pderiv_mul, pderiv_mul]
    ring
  have hp_X (x : ι) (hx : x ∈ c.support) : p ∣ X x := by
    have h := hp_pderiv x
    rw [pderiv_sumSMulXSq] at h
    have hcx : c x ≠ 0 := Finsupp.mem_support_iff.mp hx
    have hu : IsUnit (C (2 * c x) : MvPolynomial ι k) :=
      (isUnit_iff_ne_zero.mpr (mul_ne_zero two_ne_zero hcx)).map C
    exact hu.dvd_mul_left.mp h
  have hpi := hp_X i hi
  have hpj := hp_X j hj
  have hassoc : Associated p (X i : MvPolynomial ι k) :=
    hp.associated_of_dvd (X_prime (i := i)).irreducible hpi
  have : (X i : MvPolynomial ι k) ∣ X j := hassoc.symm.dvd.trans hpj
  exact hji (X_dvd_X.mp this).symm

end Field

end MvPolynomial
