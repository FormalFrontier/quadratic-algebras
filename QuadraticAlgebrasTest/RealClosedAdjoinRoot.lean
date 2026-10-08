/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.RealClosedAdjoinRoot
public import QuadraticAlgebrasTest.RealClosedModel
import Mathlib.Tactic.NormNum

/-!
# Irreducible polynomial quotient examples

Independent examples use the real-closed model and irreducible quadratic from
`QuadraticAlgebrasTest.RealClosedModel`, without using the quotient construction
to establish its hypotheses. Clients evaluate classes at both signs of the
quadratic generator and at a root selected without a supplied witness.

The linear polynomial `X` is irreducible but has a one-dimensional quotient;
the reducible quadratic and quartic of `reducibleBoundaries` cannot replace the
irreducibility hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

open Polynomial

namespace QuadraticAlgebrasTest

private instance : IsRealClosed ℝ := realIsRealClosed

private theorem gaussianMonic : (X ^ 2 + 1 : ℝ[X]).Monic := by
  simpa only [Polynomial.C_1] using
    (Polynomial.monic_X_pow_add_C (a := (1 : ℝ)) (by decide : (2 : ℕ) ≠ 0))

private theorem gaussianNonlinear : 1 < (X ^ 2 + 1 : ℝ[X]).natDegree := by
  rw [sharpGaussian.1]
  decide

private theorem nonmonicGaussianDegree :
    (C (2 : ℝ) * (X ^ 2 + 1)).natDegree = 2 := by
  rw [Polynomial.natDegree_C_mul (by norm_num : (2 : ℝ) ≠ 0)]
  exact sharpGaussian.1

/-- A nonmonic scalar multiple of `X² + 1` is still irreducible and nonlinear. -/
theorem nonmonicGaussian :
    Irreducible (C (2 : ℝ) * (X ^ 2 + 1)) ∧
      1 < (C (2 : ℝ) * (X ^ 2 + 1)).natDegree ∧
      ¬ (C (2 : ℝ) * (X ^ 2 + 1)).Monic := by
  have hunit : IsUnit (2 : ℝ) := (by norm_num : (2 : ℝ) ≠ 0).isUnit
  have hunitC : IsUnit (C (2 : ℝ) : ℝ[X]) := isUnit_C.mpr hunit
  have hirr : Irreducible (C (2 : ℝ) * (X ^ 2 + 1)) := by
    simpa only [mul_comm] using
      ((irreducible_mul_isUnit hunitC).mpr sharpGaussian.2)
  refine ⟨hirr, ?_, ?_⟩
  · rw [nonmonicGaussianDegree]
    decide
  · intro hm
    have hlc : (C (2 : ℝ) * (X ^ 2 + 1)).leadingCoeff = 2 := by
      exact gaussianMonic.leadingCoeff_C_mul 2
    have htwo : (2 : ℝ) = 1 := hlc.symm.trans hm.leadingCoeff
    norm_num at htwo

/-- Irreducibility alone does not suffice: the irreducible linear polynomial
`X` does not satisfy the degree hypothesis. -/
theorem linearBoundary :
    Irreducible (X : ℝ[X]) ∧ ¬ 1 < (X : ℝ[X]).natDegree := by
  simp [Polynomial.irreducible_X]

private theorem gaussianRoots :
    (X ^ 2 + 1 : ℝ[X]).aeval
        (QuadraticAlgebra.omega : QuadraticAlgebra ℝ (-1) 0) = 0 ∧
      (X ^ 2 + 1 : ℝ[X]).aeval
        (-(QuadraticAlgebra.omega : QuadraticAlgebra ℝ (-1) 0)) = 0 := by
  constructor <;> simp [QuadraticAlgebra.omega_pow_two_eq_add]

private theorem nonmonicGaussianRoot :
    (C (2 : ℝ) * (X ^ 2 + 1)).aeval
        (QuadraticAlgebra.omega : QuadraticAlgebra ℝ (-1) 0) = 0 := by
  simp [gaussianRoots.1]

/-- The two specified roots give different maps: their adjoined-root images
are the opposite generators of the quadratic field. -/
private theorem gaussianChoicesDiffer :
    QuadraticAlgebra.adjoinRootEquivOfRoot (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2
        sharpGaussian.1 QuadraticAlgebra.omega gaussianRoots.1
        (AdjoinRoot.root (X ^ 2 + 1 : ℝ[X])) ≠
      QuadraticAlgebra.adjoinRootEquivOfRoot (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2
        sharpGaussian.1 (-QuadraticAlgebra.omega) gaussianRoots.2
        (AdjoinRoot.root (X ^ 2 + 1 : ℝ[X])) := by
  rw [QuadraticAlgebra.adjoinRootEquivOfRoot_root,
    QuadraticAlgebra.adjoinRootEquivOfRoot_root]
  intro heq
  have him := congrArg QuadraticAlgebra.im heq
  norm_num at him

/-- Polynomial classes evaluate at the positive and negative chosen roots. -/
private theorem gaussianChosenClassValues :
    QuadraticAlgebra.adjoinRootEquivOfRoot (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2
        sharpGaussian.1 QuadraticAlgebra.omega gaussianRoots.1
        (AdjoinRoot.mk (X ^ 2 + 1 : ℝ[X]) (X + 1)) =
      (QuadraticAlgebra.omega : QuadraticAlgebra ℝ (-1) 0) + 1 ∧
    QuadraticAlgebra.adjoinRootEquivOfRoot (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2
        sharpGaussian.1 (-QuadraticAlgebra.omega) gaussianRoots.2
        (AdjoinRoot.mk (X ^ 2 + 1 : ℝ[X]) (X + 1)) =
      -(QuadraticAlgebra.omega : QuadraticAlgebra ℝ (-1) 0) + 1 := by
  constructor <;> rw [QuadraticAlgebra.adjoinRootEquivOfRoot_mk] <;> simp

/-- A polynomial class in the quotient by the nonmonic scalar multiple still
has the expected quadratic evaluation. -/
private theorem nonmonicChosenSquare :
    QuadraticAlgebra.adjoinRootEquivOfRoot
        (C (2 : ℝ) * (X ^ 2 + 1)) nonmonicGaussian.1 nonmonicGaussianDegree
        QuadraticAlgebra.omega nonmonicGaussianRoot
        (AdjoinRoot.mk (C (2 : ℝ) * (X ^ 2 + 1)) (X ^ 2)) =
      (-1 : QuadraticAlgebra ℝ (-1) 0) := by
  rw [QuadraticAlgebra.adjoinRootEquivOfRoot_mk]
  simp [QuadraticAlgebra.omega_pow_two_eq_add]

/-- The witness-free interface evaluates `X²` at its selected root of
`X² + 1`, yielding `-1` without specifying a square-root sign. -/
private theorem gaussianWitnessFreeSquare :
    QuadraticAlgebra.adjoinRootEquivOfIrreducible
        (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2 gaussianNonlinear
        (AdjoinRoot.mk (X ^ 2 + 1 : ℝ[X]) (X ^ 2)) =
      (-1 : QuadraticAlgebra ℝ (-1) 0) := by
  rw [QuadraticAlgebra.adjoinRootEquivOfIrreducible_mk]
  have hroot := QuadraticAlgebra.rootOfIrreducible_aeval
    (X ^ 2 + 1 : ℝ[X]) sharpGaussian.2
  have hsq :
      (QuadraticAlgebra.rootOfIrreducible (X ^ 2 + 1 : ℝ[X])
          sharpGaussian.2) ^ 2 = (-1 : QuadraticAlgebra ℝ (-1) 0) := by
    have hsum :
        (QuadraticAlgebra.rootOfIrreducible (X ^ 2 + 1 : ℝ[X])
          sharpGaussian.2) ^ 2 + 1 = 0 := by simpa using hroot
    exact add_eq_zero_iff_eq_neg.mp hsum
  simpa using hsq

end QuadraticAlgebrasTest
