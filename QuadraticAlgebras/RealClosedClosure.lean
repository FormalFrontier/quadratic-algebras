/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.RealClosedCoordinates
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.Sylow

/-!
# Quadratic extension of a real-closed field

The canonical quadratic algebra with generator of square `-1` is a field over a
semireal base. Over a real-closed base, it is algebraically closed, and every
irreducible polynomial over the base has degree at most two. The semireality
witness making the quadratic algebra a field is derived here, rather than
assumed from the caller.

## References

* Emil Artin and Otto Schreier, the classical real-closed-field characterization
  and odd-degree/Sylow 2-group strategy for the quadratic closure.
* Mathlib, `FieldTheory.IsRealClosed.Basic` (real-closed-field square and odd-root
  APIs) and `Analysis.Complex.Polynomial.Basic`
  (`Irreducible.natDegree_le_two`, the real-only root/minpoly degree argument).
-/

@[expose] public section

open Polynomial
open scoped IntermediateField

universe u v

namespace IsRealClosed

/-- Over a real-closed field, every sum of squares is a square. -/
theorem isSquare_of_isSumSq {R : Type u} [Field R] [IsRealClosed R]
    {s : R} (hs : IsSumSq s) : IsSquare s := by
  by_contra hnot
  obtain ⟨r, hr⟩ := isSquare_neg_of_not_isSquare hnot
  have hr0 : r ≠ 0 := by
    intro he
    apply hnot
    have hs0 : s = 0 := by simpa [he] using hr
    rw [hs0]
    exact ⟨0, by simp⟩
  have hmul : IsSumSq (s * (r⁻¹ * r⁻¹)) := hs.mul (IsSumSq.mul_self r⁻¹)
  have heq : s * (r⁻¹ * r⁻¹) = (-1 : R) := by
    have h : s = -(r * r) := by linear_combination -hr
    rw [h]
    field_simp [hr0]
  exact IsSemireal.not_isSumSq_neg_one R (heq ▸ hmul)

/-- A finite extension of odd degree of a real-closed field is trivial. -/
theorem finrank_eq_one_of_odd {R : Type u} {E : Type v} [Field R] [IsRealClosed R]
    [Field E] [Algebra R E] [FiniteDimensional R E]
    (hodd : Odd (Module.finrank R E)) : Module.finrank R E = 1 := by
  have : Algebra.IsAlgebraic R E := Algebra.IsAlgebraic.of_finite R E
  obtain ⟨x, hx⟩ := Field.exists_primitive_element R E
  have hdegree : (minpoly R x).natDegree = Module.finrank R E :=
    (Field.primitive_element_iff_minpoly_natDegree_eq R x).mp hx
  obtain ⟨a, ha⟩ := exists_isRoot_of_odd_natDegree (hdegree.symm ▸ hodd)
  have hdegree_one : (minpoly R x).natDegree = 1 := by
    by_contra hne
    exact (minpoly.irreducible (IsIntegral.of_finite R x)).not_isRoot_of_natDegree_ne_one
      hne ha
  exact hdegree.symm.trans hdegree_one

end IsRealClosed

private theorem root_of_natDegree_two_of_isSquare {F : Type u} [Field F] [NeZero (2 : F)]
    (hsq : ∀ x : F, IsSquare x) {p : F[X]} (hdegree : p.natDegree = 2) :
    ∃ x : F, p.IsRoot x := by
  have hp0 : p ≠ 0 := by
    intro he
    simp [he] at hdegree
  have hcoeff : p.coeff 2 ≠ 0 := by
    simpa [leadingCoeff, hdegree] using leadingCoeff_ne_zero.mpr hp0
  obtain ⟨s, hs⟩ := (isSquare_iff_exists_sq
    (discrim (p.coeff 2) (p.coeff 1) (p.coeff 0))).mp (hsq _)
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hcoeff
    ⟨s, by simpa only [pow_two] using hs⟩
  have hform : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
    eq_quadratic_of_degree_le_two (degree_le_of_natDegree_le hdegree.le)
  refine ⟨x, ?_⟩
  rw [Polynomial.IsRoot, hform]
  simpa [pow_two] using hx

private theorem finrank_ne_two_of_isSquare {F : Type u} {E : Type v}
    [Field F] [NeZero (2 : F)] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (hsq : ∀ x : F, IsSquare x) : Module.finrank F E ≠ 2 := by
  intro htwo
  obtain ⟨x, hx⟩ := Field.exists_primitive_element F E
  have hdegree : (minpoly F x).natDegree = 2 :=
    ((Field.primitive_element_iff_minpoly_natDegree_eq F x).mp hx).trans htwo
  obtain ⟨root, hroot⟩ := root_of_natDegree_two_of_isSquare hsq hdegree
  exact (minpoly.irreducible (IsIntegral.of_finite F x)).not_isRoot_of_natDegree_ne_one
    (by simp [hdegree]) hroot

private theorem sylow_two_eq_top {R : Type u} {E : Type v}
    [Field R] [IsRealClosed R] [Field E] [Algebra R E]
    [FiniteDimensional R E] [IsGalois R E]
    (P : Sylow 2 (E ≃ₐ[R] E)) : (P : Subgroup (E ≃ₐ[R] E)) = ⊤ := by
  have hodd_index : Odd (P : Subgroup (E ≃ₐ[R] E)).index :=
    Nat.not_even_iff_odd.mp (fun he ↦ P.not_dvd_index (even_iff_two_dvd.mp he))
  have hodd : Odd (Module.finrank R
      (IntermediateField.fixedField (P : Subgroup (E ≃ₐ[R] E)))) := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField]
    exact hodd_index
  have hbot : (IntermediateField.fixedField (P : Subgroup (E ≃ₐ[R] E))) = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp (IsRealClosed.finrank_eq_one_of_odd hodd)
  have hfix := (IntermediateField.fixingSubgroup_fixedField
    (P : Subgroup (E ≃ₐ[R] E))).symm
  simpa only [hbot, IntermediateField.fixingSubgroup_bot] using hfix

private theorem eq_top_of_isSquare {R : Type u} {E : Type v}
    [Field R] [IsRealClosed R] [Field E] [Algebra R E]
    [FiniteDimensional R E] [IsGalois R E]
    (S : IntermediateField R E) (hsq : ∀ x : S, IsSquare x) : S = ⊤ := by
  classical
  by_contra hne
  let P : Sylow 2 (E ≃ₐ[R] E) := Classical.choice inferInstance
  have hPtop : (P : Subgroup (E ≃ₐ[R] E)) = ⊤ := sylow_two_eq_top P
  have hgroup : IsPGroup 2 (E ≃ₐ[R] E) := by
    obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := m)
    simpa only [hPtop, Subgroup.card_top] using hm
  let H : Subgroup (E ≃ₐ[R] E) := S.fixingSubgroup
  obtain ⟨m, hm⟩ := (hgroup.to_subgroup H).exists_card_eq
  have hcardH : Nat.card H ≠ 1 := by
    intro he
    apply hne
    apply IntermediateField.finrank_eq_one_iff_eq_top.mp
    rw [← IsGalois.card_fixingSubgroup_eq_finrank (K := S)]
    exact he
  have hm0 : 0 < m := by
    by_contra he
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos he
    exact hcardH (by simpa [hmzero] using hm)
  have hpower : 2 ^ (m - 1) ≤ Nat.card H := by
    rw [hm]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le m 1)
  obtain ⟨J, hJH, hcardJ⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card
      Nat.prime_two hgroup hpower (H := H)
  let F : IntermediateField R E := IntermediateField.fixedField J
  have hSF : S ≤ F := by
    rw [← IsGalois.fixedField_fixingSubgroup (K := S)]
    exact IntermediateField.fixedField_le hJH
  let F' : IntermediateField S E := IntermediateField.extendScalars hSF
  have hfinF : Module.finrank F' E = Nat.card J := by
    exact IntermediateField.finrank_fixedField_eq_card (H := J)
  have hcard : Nat.card H = 2 * Nat.card J := by
    calc
      Nat.card H = 2 ^ m := hm
      _ = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel hm0]
      _ = 2 * 2 ^ (m - 1) := by rw [pow_succ]; ring
      _ = 2 * Nat.card J := by rw [hcardJ]
  have hfin : Module.finrank S F' = 2 := by
    have htower : Nat.card H = Module.finrank S F' * Nat.card J := by
      calc
        Nat.card H = Module.finrank S E := IsGalois.card_fixingSubgroup_eq_finrank S
        _ = Module.finrank S F' * Module.finrank F' E :=
          (Module.finrank_mul_finrank S F' E).symm
        _ = Module.finrank S F' * Nat.card J := by rw [hfinF]
    exact (Nat.mul_left_inj (Nat.card_pos (α := J)).ne').mp (htower.symm.trans hcard)
  have : CharZero S :=
    (RingHom.charZero_iff (algebraMap R S).injective).mp inferInstance
  exact finrank_ne_two_of_isSquare hsq hfin

namespace QuadraticAlgebra

/-- Semireality excludes a square root of `-1`, making the quadratic algebra
with generator of square `-1` a field through its existing field instance. -/
instance (R : Type u) [Field R] [IsSemireal R] : Fact (¬ IsSquare (-1 : R)) :=
  ⟨fun h ↦ IsSemireal.not_isSumSq_neg_one R h.isSumSq⟩

/-- Every element of the canonical quadratic extension of a real-closed field
has a square root in that extension. -/
theorem exists_sq_eq (R : Type u) [Field R] [IsRealClosed R]
    (z : QuadraticAlgebra R (-1) 0) :
    ∃ w : QuadraticAlgebra R (-1) 0, w ^ 2 = z := by
  obtain ⟨a, b⟩ := z
  by_cases hb : b = 0
  · subst b
    rcases IsRealClosed.isSquare_or_isSquare_neg a with ha | ha
    · obtain ⟨d, hd⟩ := (isSquare_iff_exists_sq a).mp ha
      refine ⟨⟨d, 0⟩, ?_⟩
      ext <;> simp [pow_two, hd]
    · obtain ⟨d, hd⟩ := (isSquare_iff_exists_sq (-a)).mp ha
      refine ⟨⟨0, d⟩, ?_⟩
      ext <;> simp [pow_two]
      linear_combination hd
  · have hnorm : IsSumSq (a ^ 2 + b ^ 2) := by
      simpa only [pow_two] using (IsSumSq.mul_self a).add (IsSumSq.mul_self b)
    obtain ⟨n, hn⟩ := (isSquare_iff_exists_sq (a ^ 2 + b ^ 2)).mp
      (IsRealClosed.isSquare_of_isSumSq hnorm)
    have han : a + n ≠ 0 := by
      intro he
      have he' : n = -a := by linear_combination he
      have hbzero : b ^ 2 = 0 := by rw [he'] at hn; linear_combination hn
      exact (pow_ne_zero 2 hb) hbzero
    have hchoice : ∃ n' d : R, n' ^ 2 = a ^ 2 + b ^ 2 ∧
        d ^ 2 = a + n' ∧ d ≠ 0 := by
      by_cases hsq : IsSquare (a + n)
      · obtain ⟨d, hd⟩ := (isSquare_iff_exists_sq (a + n)).mp hsq
        refine ⟨n, d, hn.symm, hd.symm, ?_⟩
        intro he
        exact han (by simpa [he] using hd)
      · obtain ⟨c, hc⟩ := (isSquare_iff_exists_sq (-(a + n))).mp
          (IsRealClosed.isSquare_neg_of_not_isSquare hsq)
        have hc0 : c ≠ 0 := by
          intro he
          have hzero : -(a + n) = 0 := by simpa [he] using hc
          apply han
          linear_combination -hzero
        have hfactor : (a - n) * c ^ 2 = b ^ 2 := by
          rw [← hc]
          linear_combination -hn
        have hd : (b / c) ^ 2 = a - n := by
          rw [div_pow, ← hfactor]
          field_simp [hc0]
        refine ⟨-n, b / c, by simpa using hn.symm,
          by simpa only [sub_eq_add_neg] using hd, div_ne_zero hb hc0⟩
    obtain ⟨n', d, hn', hd, hd0⟩ := hchoice
    obtain ⟨q, hq⟩ := (isSquare_iff_exists_sq (2 : R)).mp
      (IsRealClosed.isSquare_of_isSumSq (IsSumSq.natCast (R := R) 2))
    have hq0 : q ≠ 0 := by
      intro he
      simp [he] at hq
    have hidentity : d ^ 4 - b ^ 2 = 2 * a * d ^ 2 := by
      have hnorm' : b ^ 2 = (n' - a) * (n' + a) := by linear_combination -hn'
      rw [show d ^ 4 = (d ^ 2) ^ 2 by ring, hd, hnorm']
      ring
    have hre : (d / q) ^ 2 - (b / (q * d)) ^ 2 = a := by
      calc
        (d / q) ^ 2 - (b / (q * d)) ^ 2 =
            (d ^ 4 - b ^ 2) / (q ^ 2 * d ^ 2) := by field_simp [hq0, hd0]
        _ = (2 * a * d ^ 2) / (2 * d ^ 2) := by rw [hidentity, ← hq]
        _ = a := by field_simp [hd0]
    have him : (d / q) * (b / (q * d)) * 2 = b := by
      field_simp [hq0, hd0]
      rw [hq]
    refine ⟨⟨d / q, b / (q * d)⟩, ?_⟩
    ext
    · convert hre using 1
      simp [pow_two]
      ring
    · convert him using 1
      simp [pow_two]
      ring

/-- The quadratic extension obtained by adjoining a square root of `-1` to a
real-closed field is algebraically closed. The proof follows the classical
Artin–Schreier odd-degree and Sylow 2-group strategy, using Mathlib's
`FieldTheory.IsRealClosed.Basic` real-closed-field API. -/
instance (R : Type u) [Field R] [IsRealClosed R] :
    IsAlgClosed (QuadraticAlgebra R (-1) 0) := by
  classical
  let K := QuadraticAlgebra R (-1) 0
  let Ω := AlgebraicClosure R
  have : Algebra.IsAlgebraic R K := Algebra.IsAlgebraic.of_finite R K
  let φ : K →ₐ[R] Ω := IsAlgClosed.lift
  have hsurj : Function.Surjective φ := by
    intro x
    let T : IntermediateField R Ω := φ.fieldRange ⊔ R⟮x⟯
    have : FiniteDimensional R φ.fieldRange := φ.toLinearMap.finiteDimensional_range
    have : FiniteDimensional R (R⟮x⟯ : IntermediateField R Ω) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have : FiniteDimensional R T := IntermediateField.finiteDimensional_sup _ _
    let L : IntermediateField R Ω := IntermediateField.normalClosure R T Ω
    have : FiniteDimensional R L := inferInstance
    have : Normal R L := inferInstance
    have : IsGalois R L := ⟨⟩
    have hφL : φ.fieldRange ≤ L := by
      calc
        φ.fieldRange ≤ T := le_sup_left
        _ ≤ L := IntermediateField.le_normalClosure T
    let S : IntermediateField R L := IntermediateField.restrict hφL
    let e : K ≃ₐ[R] S := φ.equivFieldRange.trans
      (IntermediateField.restrictAlgEquiv hφL)
    have hsqS : ∀ y : S, IsSquare y := by
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      obtain ⟨w, hw⟩ := exists_sq_eq R z
      exact (isSquare_iff_exists_sq _).mpr ⟨e w, by rw [← map_pow, hw]⟩
    have htop : S = ⊤ := eq_top_of_isSquare S hsqS
    have hxT : x ∈ T :=
      (le_sup_right : R⟮x⟯ ≤ T) (IntermediateField.mem_adjoin_simple_self R x)
    have hxL : x ∈ L := IntermediateField.le_normalClosure T hxT
    let xL : L := ⟨x, hxL⟩
    have hxS : xL ∈ S := by rw [htop]; trivial
    exact (AlgHom.mem_fieldRange).mp ((IntermediateField.mem_restrict hφL xL).mp hxS)
  let e : K ≃ₐ[R] Ω := AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  exact IsAlgClosed.of_ringEquiv Ω K e.symm.toRingEquiv

end QuadraticAlgebra

namespace IsRealClosed

/-- An irreducible polynomial over a real-closed field has degree at most two.
Following the Artin–Schreier quadratic-closure result, this generalizes the
real-only root/minpoly degree argument of Mathlib's
`Analysis.Complex.Polynomial.Basic` (`Irreducible.natDegree_le_two`). -/
theorem irreducible_natDegree_le_two {R : Type u} [Field R] [IsRealClosed R]
    {p : R[X]} (hp : Irreducible p) : p.natDegree ≤ 2 := by
  obtain ⟨z, hz⟩ : ∃ z : QuadraticAlgebra R (-1) 0, p.aeval z = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne'
  have hdegree : p.natDegree = (minpoly R z).natDegree := by
    rw [minpoly.Irreducible.eq_minpoly hp hz,
      natDegree_C_mul (leadingCoeff_ne_zero.mpr hp.ne_zero)]
  rw [hdegree, ← QuadraticAlgebra.finrank_eq_two (R := R) (a := -1) (b := 0)]
  exact minpoly.natDegree_le z

end IsRealClosed
