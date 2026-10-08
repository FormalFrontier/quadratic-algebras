/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.RealClosedClosure
public import QuadraticAlgebrasTest.RealClosedModel
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Clients of real-closed quadratic closure

These examples use quadratic closure and the irreducible-degree bound.
The independent real-closed model and polynomial boundaries live in
`QuadraticAlgebrasTest.RealClosedModel` and do not import these results.

## References

* Mathlib, `Analysis.Complex.Polynomial.Basic`
  (`Irreducible.natDegree_le_two` for `ℝ[X]`), used in the comparison with
  the general real-closed degree bound.
-/

@[expose] public section

open Polynomial

namespace QuadraticAlgebrasTest

/-- The nonreal element `1 + ω` has a square root in the quadratic field. -/
theorem nonrealSquareRoot :
    (1 + QuadraticAlgebra.omega : QuadraticAlgebra ℝ (-1) 0).im ≠ 0 ∧
      ∃ z : QuadraticAlgebra ℝ (-1) 0,
        z ^ 2 = 1 + QuadraticAlgebra.omega := by
  have : IsRealClosed ℝ := realIsRealClosed
  constructor
  · simp [QuadraticAlgebra.im_add, QuadraticAlgebra.im_one]
  · exact IsAlgClosed.exists_pow_nat_eq (1 + QuadraticAlgebra.omega) (by decide : 0 < 2)

/-- A cubic over the quadratic extension has a root. -/
theorem nonconstantPolynomialRoot :
    ∃ z : QuadraticAlgebra ℝ (-1) 0,
      (X ^ 3 - C (1 + QuadraticAlgebra.omega) :
        (QuadraticAlgebra ℝ (-1) 0)[X]).IsRoot z := by
  have : IsRealClosed ℝ := realIsRealClosed
  apply IsAlgClosed.exists_root
  rw [Polynomial.degree_X_pow_sub_C (by decide : 0 < 3)
    (1 + QuadraticAlgebra.omega : QuadraticAlgebra ℝ (-1) 0)]
  decide

/-- The general degree bound is attained by `X² + 1` over the reals. -/
theorem sharpGenericBound :
    (X ^ 2 + 1 : ℝ[X]).natDegree = 2 ∧
      (X ^ 2 + 1 : ℝ[X]).natDegree ≤ 2 := by
  have : IsRealClosed ℝ := realIsRealClosed
  exact ⟨sharpGaussian.1, IsRealClosed.irreducible_natDegree_le_two sharpGaussian.2⟩

/-- The generic real-closed bound agrees with Mathlib's real-only degree bound. -/
theorem realBoundComparison {p : ℝ[X]} (hp : Irreducible p) :
    p.natDegree ≤ 2 ∧ p.degree ≤ 2 := by
  have : IsRealClosed ℝ := realIsRealClosed
  exact ⟨IsRealClosed.irreducible_natDegree_le_two hp,
    Polynomial.natDegree_le_iff_degree_le.mp hp.natDegree_le_two⟩

end QuadraticAlgebrasTest
