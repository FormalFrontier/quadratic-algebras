/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Integral elements in quadratic algebras

This file descends the trace and norm of an integral element of a quadratic
algebra over a fraction field.  The defining quadratic algebra need not be a
domain: conjugation preserves integrality, so the trace and norm are integral
over the base ring, and integral closedness places them back in that ring.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.H, supplies the trace-and-norm descent proof route;
  the statements here do not require a domain quadratic algebra.
* Mathlib's [integral-closure API](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean)
  identifies integral elements of a fraction field with base-ring elements.
-/

public section

set_option warningAsError true

noncomputable section

namespace QuadraticAlgebra

universe u v

variable {R : Type u} {K : Type v}

/-- Quadratic conjugation as an algebra automorphism over any ring acting
through the coefficient ring. -/
@[expose]
noncomputable def starAlgEquiv (R : Type u) [CommRing R] [CommRing K]
    [Algebra R K] (a b : K) :
    QuadraticAlgebra K a b ≃ₐ[R] QuadraticAlgebra K a b :=
  { starRingAut with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R K]
      ext <;> simp }

/-- The algebra automorphism `starAlgEquiv` acts by quadratic conjugation. -/
@[simp]
theorem starAlgEquiv_apply (R : Type u) [CommRing R] [CommRing K]
    [Algebra R K] (a b : K) (x : QuadraticAlgebra K a b) :
    starAlgEquiv R a b x = star x :=
  rfl

/-- Conjugating a quadratic element preserves integrality over the base ring,
without requiring the quadratic algebra or coefficient ring to be a domain. -/
theorem isIntegral_star [CommRing R] [CommRing K] [Algebra R K]
    {a b : K} {x : QuadraticAlgebra K a b}
    (hx : IsIntegral R x) : IsIntegral R (star x) := by
  simpa using hx.map (starAlgEquiv R a b)

variable [CommRing R] [IsIntegrallyClosed R] [CommRing K] [Algebra R K]
  [IsFractionRing R K]
  {a b : K}

/-- The trace of an integral quadratic element over an integrally closed base
ring belongs to that base ring. This trace-descent step follows Vakil,
*The Rising Sea*, Exercise 5.4.H, without requiring a domain quadratic algebra. -/
theorem isInteger_trace_of_isIntegral {x : QuadraticAlgebra K a b}
    (hx : IsIntegral R x) : IsLocalization.IsInteger R (trace x) := by
  have hmap : IsIntegral R (algebraMap K (QuadraticAlgebra K a b) (trace x)) := by
    rw [algebraMap_trace_eq_add_star]
    exact hx.add (isIntegral_star (R := R) hx)
  have htrace : IsIntegral R (trace x) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K (QuadraticAlgebra K a b))
      algebraMap_injective).mp hmap
  exact IsIntegrallyClosed.isIntegral_iff.mp htrace

/-- The norm of an integral quadratic element over an integrally closed base
ring belongs to that base ring. This norm-descent step follows Vakil,
*The Rising Sea*, Exercise 5.4.H, without requiring a domain quadratic algebra. -/
theorem isInteger_norm_of_isIntegral {x : QuadraticAlgebra K a b}
    (hx : IsIntegral R x) : IsLocalization.IsInteger R (norm x) := by
  have hmap : IsIntegral R (algebraMap K (QuadraticAlgebra K a b) (norm x)) := by
    rw [algebraMap_norm_eq_mul_star]
    exact hx.mul (isIntegral_star (R := R) hx)
  have hnorm : IsIntegral R (norm x) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K (QuadraticAlgebra K a b))
      algebraMap_injective).mp hmap
  exact IsIntegrallyClosed.isIntegral_iff.mp hnorm

end QuadraticAlgebra
