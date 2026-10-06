/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.AdjoinRoot
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-!
# Chosen negative-discriminant coordinates for quadratic algebras

An irreducible defining quadratic over a real-closed field has a chosen square
root of the negative discriminant. A supplied nonzero square root also gives
coordinates over any field in which two is nonzero. The coordinates depend on
the chosen root: there is no preferred sign without an additional choice.
Nonsplitting belongs to the irreducible real-closed layer; the supplied-witness
coordinates may also describe split quadratics.

The quotient-coordinate interface uses the existing `AdjoinRoot` bridge and
applies to monic quadratics of degree two. No assertion about irreducible
polynomials of higher degree is made here.

## References

* Mathlib's `FieldTheory.IsRealClosed.Basic` provides
  `IsRealClosed.isSquare_neg_of_not_isSquare`; its
  `Algebra.QuadraticAlgebra.Discriminant` provides
  `QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr` and `QuadraticAlgebra.discr`.
  These are the pinned Mathlib arguments for the real-closed witness.
* Mathlib's `QuadraticAlgebra.changeGeneratorEquiv` and
  `Polynomial.eq_quadratic_of_degree_le_two` provide the coordinate change
  and monic-degree-two polynomial identity.
* The `QuadraticAlgebra.equivAdjoinRoot` bridge in this library.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false
set_option warningAsError true

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [Field R]

private theorem definingPolynomial_natDegree (a b : R) :
    (definingPolynomial a b).natDegree = 2 := by
  have hpoly : definingPolynomial a b =
      C (1 : R) * X ^ 2 + C (-b) * X + C (-a) := by
    simp only [definingPolynomial, Polynomial.C_1, one_mul, map_neg]
    ring
  rw [hpoly]
  exact natDegree_quadratic one_ne_zero

/-- Irreducibility of the defining quadratic over a real-closed field gives a
nonzero square root of the negative discriminant `-(b ^ 2 + 4 * a)`.
Mathlib's `QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr` rules out a square
discriminant, then `IsRealClosed.isSquare_neg_of_not_isSquare` supplies its
negative square root. No order or orientation of this root is specified. -/
theorem exists_sq_eq_neg_discr_of_irreducible [IsRealClosed R] (a b : R)
    (hirr : Irreducible (definingPolynomial a b)) :
    ∃ d : R, d ≠ 0 ∧ d ^ 2 = -(discr a b) := by
  have hnot : ¬ IsSquare (discr a b) := by
    intro hsquare
    let : Invertible (2 : R) := invertibleOfNonzero two_ne_zero
    obtain ⟨root, hroot⟩ :=
      (exists_sq_eq_iff_isSquare_discr (a := a) (b := b)).mpr hsquare
    have hp_root : (definingPolynomial a b).IsRoot root := by
      simp [Polynomial.IsRoot, definingPolynomial, hroot, add_comm]
    exact (hirr.not_isRoot_of_natDegree_ne_one
      (by rw [definingPolynomial_natDegree]; decide)) hp_root
  obtain ⟨d, hd_sq⟩ :=
    (isSquare_iff_exists_sq (-(discr a b))).mp
      (IsRealClosed.isSquare_neg_of_not_isSquare hnot)
  have hd : d ≠ 0 := by
    intro heq
    subst d
    have hzero : discr a b = 0 := by simpa using hd_sq
    exact hnot (by simp [hzero])
  exact ⟨d, hd, hd_sq.symm⟩

/-- Coordinates determined by a *supplied* nonzero square root of the negative
discriminant. The intended change of generator from the target parameters
`(-1, 0)` has unit scale `d / 2` and translation `b / 2`. -/
noncomputable def equivOfDiscrSqNeg [NeZero (2 : R)] (a b d : R) (hd : d ≠ 0)
    (hd_sq : d ^ 2 = -(discr a b)) :
    QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R (-1) 0 := by
  have hdiscr : d ^ 2 + b ^ 2 + 4 * a = 0 := by
    rw [discr_def] at hd_sq
    linear_combination hd_sq
  have ha : a = (d / 2) ^ 2 * (-1) - (d / 2) * (0 : R) * (b / 2) - (b / 2) ^ 2 := by
    simp only [mul_zero]
    field_simp [two_ne_zero]
    linear_combination hdiscr
  have hb : b = (d / 2) * (0 : R) + 2 * (b / 2) := by
    simp only [mul_zero, zero_add]
    field_simp [two_ne_zero]
  exact changeGeneratorEquiv (-1 : R) 0
    (Units.mk0 (d / 2) (div_ne_zero hd two_ne_zero)) (b / 2) ha hb

/-- The chosen coordinates send the old generator to the specified affine
expression in the generator with square `-1`. -/
@[simp]
theorem equivOfDiscrSqNeg_omega [NeZero (2 : R)] (a b d : R) (hd : d ≠ 0)
    (hd_sq : d ^ 2 = -(discr a b)) :
    equivOfDiscrSqNeg a b d hd hd_sq omega =
      (d / 2) • (omega : QuadraticAlgebra R (-1) 0) +
        algebraMap R (QuadraticAlgebra R (-1) 0) (b / 2) := by
  have hdiscr : d ^ 2 + b ^ 2 + 4 * a = 0 := by
    rw [discr_def] at hd_sq
    linear_combination hd_sq
  have ha : a = (d / 2) ^ 2 * (-1) - (d / 2) * (0 : R) * (b / 2) - (b / 2) ^ 2 := by
    simp only [mul_zero]
    field_simp [two_ne_zero]
    linear_combination hdiscr
  have hb : b = (d / 2) * (0 : R) + 2 * (b / 2) := by
    simp only [mul_zero, zero_add]
    field_simp [two_ne_zero]
  change changeGenerator (-1 : R) 0 (d / 2) (b / 2) ha hb omega = _
  exact changeGenerator_omega (-1 : R) 0 (d / 2) (b / 2) ha hb

/-- Choosing the opposite square root conjugates the image of the generator;
the resulting coordinate maps are not identified. -/
theorem equivOfDiscrSqNeg_neg_omega [NeZero (2 : R)] (a b d : R) (hd : d ≠ 0)
    (hd_sq : d ^ 2 = -(discr a b)) :
    equivOfDiscrSqNeg a b (-d) (neg_ne_zero.mpr hd)
        (by simpa using hd_sq) omega =
      star (equivOfDiscrSqNeg a b d hd hd_sq omega) := by
  simp only [equivOfDiscrSqNeg_omega]
  ext <;> simp only [re_star, im_star, re_add, im_add, re_smul, im_smul,
    re_omega, im_omega, algebraMap_eq, smul_eq_mul] <;> ring

/-- Coordinates for the existing quotient by a monic quadratic of degree two.
The chosen witness has square the negative discriminant of the coefficient
form `p = definingPolynomial (-p.coeff 0) (-p.coeff 1)`. Irreducibility is not
needed once that witness is supplied. -/
noncomputable def adjoinRootEquivOfDiscrSqNeg [NeZero (2 : R)] (p : R[X]) (hp : p.Monic)
    (hdeg : p.natDegree = 2) (d : R) (hd : d ≠ 0)
    (hd_sq : d ^ 2 = -(discr (-p.coeff 0) (-p.coeff 1))) :
    AdjoinRoot p ≃ₐ[R] QuadraticAlgebra R (-1) 0 := by
  have hcoeff : p.coeff 2 = 1 := by
    simpa only [hdeg] using hp.coeff_natDegree
  have heq : p = definingPolynomial (-p.coeff 0) (-p.coeff 1) := by
    calc
      p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
        eq_quadratic_of_degree_le_two (degree_le_of_natDegree_le hdeg.le)
      _ = definingPolynomial (-p.coeff 0) (-p.coeff 1) := by
        rw [hcoeff]
        simp only [definingPolynomial, Polynomial.C_1, one_mul, map_neg]
        ring
  exact (AdjoinRoot.algEquivOfEq R p
      (definingPolynomial (-p.coeff 0) (-p.coeff 1))
      heq).trans
    ((equivAdjoinRoot (-p.coeff 0) (-p.coeff 1)).symm.trans
      (equivOfDiscrSqNeg (-p.coeff 0) (-p.coeff 1) d hd hd_sq))

/-- The specified root is sent to its chosen affine quadratic coordinate. -/
@[simp]
theorem adjoinRootEquivOfDiscrSqNeg_root [NeZero (2 : R)] (p : R[X]) (hp : p.Monic)
    (hdeg : p.natDegree = 2) (d : R) (hd : d ≠ 0)
    (hd_sq : d ^ 2 = -(discr (-p.coeff 0) (-p.coeff 1))) :
    adjoinRootEquivOfDiscrSqNeg p hp hdeg d hd hd_sq (AdjoinRoot.root p) =
      (d / 2) • (omega : QuadraticAlgebra R (-1) 0) +
        algebraMap R (QuadraticAlgebra R (-1) 0) ((-p.coeff 1) / 2) := by
  simp only [adjoinRootEquivOfDiscrSqNeg, AlgEquiv.trans_apply,
    AdjoinRoot.algEquivOfEq_root, equivAdjoinRoot_symm_apply_root,
    equivOfDiscrSqNeg_omega]

/-- Evaluate any polynomial class at the chosen image of the adjoined root. -/
theorem adjoinRootEquivOfDiscrSqNeg_mk [NeZero (2 : R)] (p : R[X]) (hp : p.Monic)
    (hdeg : p.natDegree = 2) (d : R) (hd : d ≠ 0)
    (hd_sq : d ^ 2 = -(discr (-p.coeff 0) (-p.coeff 1))) (g : R[X]) :
    adjoinRootEquivOfDiscrSqNeg p hp hdeg d hd hd_sq (AdjoinRoot.mk p g) =
      g.eval₂ (algebraMap R (QuadraticAlgebra R (-1) 0))
        ((d / 2) • (omega : QuadraticAlgebra R (-1) 0) +
          algebraMap R (QuadraticAlgebra R (-1) 0) ((-p.coeff 1) / 2)) := by
  let coord := adjoinRootEquivOfDiscrSqNeg p hp hdeg d hd hd_sq
  calc
    coord (AdjoinRoot.mk p g) = coord (aeval (AdjoinRoot.root p) g) := by
      rw [AdjoinRoot.aeval_eq]
    _ = g.eval₂ (algebraMap R (QuadraticAlgebra R (-1) 0))
          (coord (AdjoinRoot.root p)) := by
      rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]
    _ = _ := by
      exact congrArg (g.eval₂ (algebraMap R (QuadraticAlgebra R (-1) 0)))
        (adjoinRootEquivOfDiscrSqNeg_root p hp hdeg d hd hd_sq)

end QuadraticAlgebra
