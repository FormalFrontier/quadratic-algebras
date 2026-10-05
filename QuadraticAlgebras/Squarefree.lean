/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree denominators in fraction fields

This file records the denominator argument used in quadratic integral-closure
criteria.  If `f` is squarefree in a unique factorization domain and `x² f`
lies in the base ring, then the reduced denominator of `x` must be a unit.

The result is stated for an arbitrary chosen fraction field.  It is not tied
to a quadratic-algebra presentation.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.H, supplies the reduced-denominator proof route;
  this lemma applies to an arbitrary chosen fraction field.
* Mathlib's [numerator and denominator API](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/Localization/NumDen.lean)
  provides reduced fractions over a UFD.
-/

public section

set_option warningAsError true

namespace IsFractionRing

variable {A K : Type*} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- If the square of a fraction times a squarefree base-ring element belongs
to the image of the base ring, then the fraction itself belongs to that image.
Here `IsLocalization.IsInteger` means base-ring membership, not `IsIntegral`.
The reduced-denominator argument follows Vakil, *The Rising Sea*, Exercise
5.4.H, in this more general fraction-field setting. -/
theorem isInteger_of_sq_mul_squarefree
    {f : A} (hf : Squarefree f) {x : K}
    (hx : IsLocalization.IsInteger A (x ^ 2 * algebraMap A K f)) :
    IsLocalization.IsInteger A x := by
  obtain ⟨v, hv⟩ := hx
  have hden : x * algebraMap A K (den A x) = algebraMap A K (num A x) :=
    (num_mul_den_eq_num_iff_eq (x := x) (y := x)).2 rfl
  have hdiv : (den A x : A) * den A x ∣ num A x * num A x * f := by
    refine ⟨v, (FaithfulSMul.algebraMap_injective A K) ?_⟩
    simp only [map_mul]
    rw [← hden, hv]
    ring
  have hden_dvd : (den A x : A) ∣ num A x * num A x := by
    apply hf.dvd_of_squarefree_of_mul_dvd_mul_right
    simpa only [mul_comm] using hdiv
  have hden_unit : IsUnit (den A x : A) :=
    ((num_den_reduced A x).mul_left
      (num_den_reduced A x)).symm.isUnit_of_dvd hden_dvd
  exact isInteger_of_isUnit_den hden_unit

end IsFractionRing
