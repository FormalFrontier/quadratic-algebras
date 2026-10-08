/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.RealComplexAdjoinRoot
import QuadraticAlgebrasTest.RealClosedModel
import Mathlib.Tactic.NormNum

/-!
# Complex-coordinate and real-polynomial quotient examples

The Gaussian irreducibility and degree facts are independent of the complex
equivalences; they use the existing real-polynomial model. The calculations
involving equivalences use their characteristic coordinate and class laws.
The ideal-quotient example identifies `AdjoinRoot`'s polynomial variable with
the class of `X` under its defining presentation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

open Polynomial

namespace QuadraticAlgebrasTest

/-- Both imaginary units are roots of the Gaussian quadratic over `ℝ`. -/
theorem gaussianComplexRoots :
    (X ^ 2 + 1 : ℝ[X]).aeval Complex.I = 0 ∧
      (X ^ 2 + 1 : ℝ[X]).aeval (-Complex.I) = 0 := by
  constructor <;> simp [Complex.I_sq]

/-- The nonzero scalar multiple `3 * (X² + 1)` is irreducible and quadratic
but not monic. -/
theorem scaledGaussian :
    Irreducible (C (3 : ℝ) * (X ^ 2 + 1)) ∧
      (C (3 : ℝ) * (X ^ 2 + 1)).natDegree = 2 ∧
      ¬ (C (3 : ℝ) * (X ^ 2 + 1)).Monic := by
  have hunit : IsUnit (3 : ℝ) := (by norm_num : (3 : ℝ) ≠ 0).isUnit
  have hunitC : IsUnit (C (3 : ℝ) : ℝ[X]) := isUnit_C.mpr hunit
  have hmonic : (X ^ 2 + 1 : ℝ[X]).Monic := by
    simpa only [Polynomial.C_1] using
      (Polynomial.monic_X_pow_add_C (a := (1 : ℝ)) (by decide : (2 : ℕ) ≠ 0))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mul_comm] using
      ((irreducible_mul_isUnit hunitC).mpr sharpGaussian.2)
  · rw [Polynomial.natDegree_C_mul (by norm_num : (3 : ℝ) ≠ 0)]
    exact sharpGaussian.1
  · intro hscaled
    have hleading : (C (3 : ℝ) * (X ^ 2 + 1)).leadingCoeff = 3 :=
      hmonic.leadingCoeff_C_mul 3
    have heq : (3 : ℝ) = 1 := hleading.symm.trans hscaled.leadingCoeff
    norm_num at heq

private theorem nonlinearGaussian : 1 < (X ^ 2 + 1 : ℝ[X]).natDegree := by
  rw [sharpGaussian.1]
  decide

private theorem nonlinearScaledGaussian :
    1 < (C (3 : ℝ) * (X ^ 2 + 1)).natDegree := by
  rw [scaledGaussian.2.1]
  decide

private theorem linearAndReducibleBoundaries :
    Irreducible (X : ℝ[X]) ∧ ¬ 1 < (X : ℝ[X]).natDegree ∧
      ¬ Irreducible (X ^ 2 - 1 : ℝ[X]) ∧
      ¬ Irreducible (X ^ 4 - 1 : ℝ[X]) := by
  exact ⟨by simp [Polynomial.irreducible_X], by simp,
    reducibleBoundaries.1, reducibleBoundaries.2.2⟩

/-- The forward and inverse coordinate rules agree with the Gaussian
generator and give a nontrivial pair of coordinates. -/
private theorem complexCoordinateClient :
    QuadraticAlgebra.realComplexEquiv
        (⟨2, 3⟩ : QuadraticAlgebra ℝ (-1) 0) = (2 : ℂ) + 3 * Complex.I ∧
      (QuadraticAlgebra.realComplexEquiv.symm ((2 : ℂ) + 3 * Complex.I)).im = 3 := by
  constructor
  · rw [QuadraticAlgebra.realComplexEquiv_apply]
    rfl
  · rw [QuadraticAlgebra.realComplexEquiv_symm_apply]
    simp

/-- Either imaginary-unit root evaluates a Gaussian polynomial class, with
different images for `X + 1`. -/
private theorem gaussianRootChoices :
    QuadraticAlgebra.adjoinRootComplexEquivOfRoot (X ^ 2 + 1 : ℝ[X])
        sharpGaussian.2 sharpGaussian.1 Complex.I gaussianComplexRoots.1
        (AdjoinRoot.mk (X ^ 2 + 1 : ℝ[X]) (X + 1)) = Complex.I + 1 ∧
      QuadraticAlgebra.adjoinRootComplexEquivOfRoot (X ^ 2 + 1 : ℝ[X])
        sharpGaussian.2 sharpGaussian.1 (-Complex.I) gaussianComplexRoots.2
        (AdjoinRoot.mk (X ^ 2 + 1 : ℝ[X]) (X + 1)) = -Complex.I + 1 := by
  constructor <;> rw [QuadraticAlgebra.adjoinRootComplexEquivOfRoot_mk] <;> simp

/-- The all-class law respects real coefficients and multiplication by the
class of the polynomial variable. -/
private theorem gaussianAffineClass :
    QuadraticAlgebra.adjoinRootComplexEquivOfRoot (X ^ 2 + 1 : ℝ[X])
        sharpGaussian.2 sharpGaussian.1 Complex.I gaussianComplexRoots.1
        (AdjoinRoot.mk (X ^ 2 + 1 : ℝ[X]) (C 7 * X + C 2)) =
      (7 : ℂ) * Complex.I + 2 := by
  rw [QuadraticAlgebra.adjoinRootComplexEquivOfRoot_mk]
  simp

/-- The two supplied-root maps differ even though the quotient and defining
polynomial are the same. -/
private theorem gaussianChoicesDiffer :
    QuadraticAlgebra.adjoinRootComplexEquivOfRoot (X ^ 2 + 1 : ℝ[X])
        sharpGaussian.2 sharpGaussian.1 Complex.I gaussianComplexRoots.1
        (AdjoinRoot.root (X ^ 2 + 1 : ℝ[X])) ≠
      QuadraticAlgebra.adjoinRootComplexEquivOfRoot (X ^ 2 + 1 : ℝ[X])
        sharpGaussian.2 sharpGaussian.1 (-Complex.I) gaussianComplexRoots.2
        (AdjoinRoot.root (X ^ 2 + 1 : ℝ[X])) := by
  rw [QuadraticAlgebra.adjoinRootComplexEquivOfRoot_root,
    QuadraticAlgebra.adjoinRootComplexEquivOfRoot_root]
  intro heq
  have him := congrArg Complex.im heq
  norm_num at him

/-- The algebra equivalence sends the ideal-quotient class of `X` to
the specified complex root. -/
private theorem idealQuotientVariable :
    QuadraticAlgebra.adjoinRootComplexEquivOfRoot (X ^ 2 + 1 : ℝ[X])
        sharpGaussian.2 sharpGaussian.1 Complex.I gaussianComplexRoots.1
        (Ideal.Quotient.mk (Ideal.span {(X ^ 2 + 1 : ℝ[X])}) X) = Complex.I := by
  change QuadraticAlgebra.adjoinRootComplexEquivOfRoot (X ^ 2 + 1 : ℝ[X])
    sharpGaussian.2 sharpGaussian.1 Complex.I gaussianComplexRoots.1
    (AdjoinRoot.root (X ^ 2 + 1 : ℝ[X])) = Complex.I
  exact QuadraticAlgebra.adjoinRootComplexEquivOfRoot_root _ _ _ _ _

/-- Scalar multiplication does not require normalizing the defining
polynomial to monic form before evaluating its quotient class. -/
private theorem scaledGaussianSquare :
    QuadraticAlgebra.adjoinRootComplexEquivOfRoot (C (3 : ℝ) * (X ^ 2 + 1))
        scaledGaussian.1 scaledGaussian.2.1 Complex.I (by simp [gaussianComplexRoots.1])
        (AdjoinRoot.mk (C (3 : ℝ) * (X ^ 2 + 1)) (X ^ 2)) = (-1 : ℂ) := by
  rw [QuadraticAlgebra.adjoinRootComplexEquivOfRoot_mk]
  simp [Complex.I_sq]

/-- Without selecting the sign of a root, its square still evaluates to
`-1` in the Gaussian quotient. -/
private theorem witnessFreeGaussianSquare :
    QuadraticAlgebra.adjoinRootComplexEquivOfIrreducible
        (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2 nonlinearGaussian
        (AdjoinRoot.mk (X ^ 2 + 1 : ℝ[X]) (X ^ 2)) = (-1 : ℂ) := by
  rw [QuadraticAlgebra.adjoinRootComplexEquivOfIrreducible_mk]
  have hroot := QuadraticAlgebra.complexRootOfIrreducible_aeval
    (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2
  have hsquare : (QuadraticAlgebra.complexRootOfIrreducible
      (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2) ^ 2 + 1 = 0 := by
    simpa using hroot
  simpa using (add_eq_zero_iff_eq_neg.mp hsquare)

/-- The nonlinear, nonmonic example also supplies valid inputs to the
root-free quotient interface. -/
private theorem witnessFreeScaledGaussianSquare :
    QuadraticAlgebra.adjoinRootComplexEquivOfIrreducible
        (C (3 : ℝ) * (X ^ 2 + 1)) scaledGaussian.1 nonlinearScaledGaussian
        (AdjoinRoot.mk (C (3 : ℝ) * (X ^ 2 + 1)) (X ^ 2)) = (-1 : ℂ) := by
  rw [QuadraticAlgebra.adjoinRootComplexEquivOfIrreducible_mk]
  have hroot := QuadraticAlgebra.complexRootOfIrreducible_aeval
    (C (3 : ℝ) * (X ^ 2 + 1)) scaledGaussian.1
  have hsquare : (QuadraticAlgebra.complexRootOfIrreducible
      (C (3 : ℝ) * (X ^ 2 + 1)) scaledGaussian.1) ^ 2 + 1 = 0 := by
    have hz : (3 : ℂ) *
        ((QuadraticAlgebra.complexRootOfIrreducible
          (C (3 : ℝ) * (X ^ 2 + 1)) scaledGaussian.1) ^ 2 + 1) = 0 := by
      simpa using hroot
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  simpa using (add_eq_zero_iff_eq_neg.mp hsquare)

end QuadraticAlgebrasTest
