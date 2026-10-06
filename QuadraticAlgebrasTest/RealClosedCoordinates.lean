/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.RealClosedCoordinates
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit quadratic witnesses and boundary cases

The rational witness calculations and the semireal and reducible boundaries
use existing arithmetic and polynomial APIs. The real-closed specialization
depends on the witness theorem; the coordinate computations depend on the
chosen-equivalence and evaluation laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false
set_option warningAsError true

noncomputable section

open Polynomial

namespace QuadraticAlgebrasTest

universe u

private theorem gaussianPolynomial :
    QuadraticAlgebra.definingPolynomial (-1 : ℚ) 0 = (X ^ 2 + 1 : ℚ[X]) := by
  simp [QuadraticAlgebra.definingPolynomial]

private theorem translatedPolynomial :
    QuadraticAlgebra.definingPolynomial (-2 : ℚ) 2 =
      (X ^ 2 - C (2 : ℚ) * X + C (2 : ℚ) : ℚ[X]) := by
  simp [QuadraticAlgebra.definingPolynomial]
  ring

/-- The rational number `2` is a nonzero square root of the negative
discriminant of the quadratic with generator of square `-1`. -/
public theorem gaussianWitness :
    (2 : ℚ) ≠ 0 ∧ (2 : ℚ) ^ 2 = -(QuadraticAlgebra.discr (-1) 0) := by
  norm_num [QuadraticAlgebra.discr]

private theorem translatedWitness :
    (2 : ℚ) ≠ 0 ∧ (2 : ℚ) ^ 2 = -(QuadraticAlgebra.discr (-2) 2) := by
  norm_num [QuadraticAlgebra.discr]

private theorem oppositeGaussianWitness :
    (-2 : ℚ) ≠ 0 ∧ (-2 : ℚ) ^ 2 = -(QuadraticAlgebra.discr (-1) 0) := by
  norm_num [QuadraticAlgebra.discr]

private theorem gaussianRootFree (R : Type u) [Field R] [IsSemireal R] (r : R) :
    ¬ (X ^ 2 + 1 : R[X]).IsRoot r := by
  intro hr
  have hr_sq : r ^ 2 = -1 := by
    simpa [Polynomial.IsRoot, add_eq_zero_iff_eq_neg] using hr
  exact IsSemireal.not_isSumSq_neg_one R
    ((show IsSquare (-1 : R) from ⟨r, by simpa only [pow_two] using hr_sq.symm⟩).isSumSq)

private theorem gaussianIrreducible (R : Type u) [Field R] [IsSemireal R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      simpa only [Polynomial.C_1] using
        (Polynomial.natDegree_X_pow_add_C (r := (1 : R)) (n := 2))
    rw [hdeg]
    decide
  · exact gaussianRootFree R

private theorem gaussianRealClosedWitness (R : Type u) [Field R] [IsRealClosed R] :
    ∃ d : R, d ≠ 0 ∧ d ^ 2 = 4 := by
  have hirr : Irreducible (QuadraticAlgebra.definingPolynomial (-1 : R) 0) := by
    simpa [QuadraticAlgebra.definingPolynomial] using gaussianIrreducible R
  simpa [QuadraticAlgebra.discr] using
    QuadraticAlgebra.exists_sq_eq_neg_discr_of_irreducible (-1 : R) 0 hirr

private theorem splitQuadraticReducible (R : Type u) [Field R] :
    ¬ Irreducible (QuadraticAlgebra.definingPolynomial (1 : R) 0) := by
  intro hirr
  have hp : QuadraticAlgebra.definingPolynomial (1 : R) 0 = X ^ 2 - C 1 := by
    simp [QuadraticAlgebra.definingPolynomial]
  have hdegree : (QuadraticAlgebra.definingPolynomial (1 : R) 0).natDegree ≠ 1 := by
    rw [hp, Polynomial.natDegree_X_pow_sub_C]
    decide
  have hroot : (QuadraticAlgebra.definingPolynomial (1 : R) 0).IsRoot (1 : R) := by
    rw [hp]
    simp [Polynomial.IsRoot]
  exact (hirr.not_isRoot_of_natDegree_ne_one hdegree) hroot

private theorem translatedChosenGenerator :
    QuadraticAlgebra.equivOfDiscrSqNeg (-2 : ℚ) 2 2
        translatedWitness.1 translatedWitness.2
        (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-2) 2) =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-1) 0) + 1 := by
  simp [QuadraticAlgebra.equivOfDiscrSqNeg_omega]

private theorem oppositeGaussianGenerator :
    QuadraticAlgebra.equivOfDiscrSqNeg (-1 : ℚ) 0 (-2)
        oppositeGaussianWitness.1 oppositeGaussianWitness.2
        (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-1) 0) =
      -(QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-1) 0) := by
  simp [QuadraticAlgebra.equivOfDiscrSqNeg_omega]

private theorem gaussianMonic : (X ^ 2 + 1 : ℚ[X]).Monic := by
  simpa only [Polynomial.C_1] using
    (Polynomial.monic_X_pow_add_C (a := (1 : ℚ)) (by decide : (2 : ℕ) ≠ 0))

private theorem gaussianDegree : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by
  simpa only [Polynomial.C_1] using
    (Polynomial.natDegree_X_pow_add_C (r := (1 : ℚ)) (n := 2))

private theorem gaussianQuotientWitness :
    (2 : ℚ) ^ 2 = -(QuadraticAlgebra.discr
      (-(X ^ 2 + 1 : ℚ[X]).coeff 0) (-(X ^ 2 + 1 : ℚ[X]).coeff 1)) := by
  norm_num [QuadraticAlgebra.discr, Polynomial.coeff_one]

private theorem gaussianQuotientSquare :
    QuadraticAlgebra.adjoinRootEquivOfDiscrSqNeg (X ^ 2 + 1 : ℚ[X])
        gaussianMonic gaussianDegree 2 (by norm_num) gaussianQuotientWitness
        (AdjoinRoot.mk (X ^ 2 + 1 : ℚ[X]) (X ^ 2)) =
      -1 := by
  have hcoeff : (X ^ 2 + 1 : ℚ[X]).coeff 1 = 0 := by
    simp [Polynomial.coeff_one]
  have hcoordinate :
      (2 / 2 : ℚ) • (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-1) 0) +
        algebraMap ℚ (QuadraticAlgebra ℚ (-1) 0)
          ((-(X ^ 2 + 1 : ℚ[X]).coeff 1) / 2) =
        (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-1) 0) := by
    norm_num [hcoeff]
  calc
    _ = ((2 / 2 : ℚ) • (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-1) 0) +
          algebraMap ℚ (QuadraticAlgebra ℚ (-1) 0)
            ((-(X ^ 2 + 1 : ℚ[X]).coeff 1) / 2)) ^ 2 := by
      simp
    _ = (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-1) 0) ^ 2 := by
      rw [hcoordinate]
    _ = -1 := by
      simpa [Algebra.smul_def] using
        (QuadraticAlgebra.omega_pow_two_eq_add
          (R := ℚ) (a := (-1 : ℚ)) (b := (0 : ℚ)))

end QuadraticAlgebrasTest
