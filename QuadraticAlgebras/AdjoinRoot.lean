/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Quadratic algebras as polynomial quotients

This file identifies mathlib's coordinate model `QuadraticAlgebra R a b`, in
which `omega ^ 2 = a + b * omega`, with the corresponding `AdjoinRoot` of
`X ^ 2 - b * X - a`.

## References

* Mathlib's [quadratic algebra](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/QuadraticAlgebra/Basic.lean)
  and [adjoined roots](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/AdjoinRoot.lean)
  provide the two presentations identified here.
* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.H, motivates the quadratic integral-closure setting;
  the equivalence here works over arbitrary commutative rings.
-/

public section

set_option warningAsError true

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [CommRing R]

/-- The monic polynomial defining `QuadraticAlgebra R a b`. -/
@[expose]
def definingPolynomial (a b : R) : R[X] :=
  X ^ 2 - (C b * X + C a)

/-- The defining quadratic is monic over every commutative ring. -/
theorem definingPolynomial_monic (a b : R) :
    (definingPolynomial a b).Monic := by
  exact monic_X_pow_sub degree_linear_lt

/-- The canonical map from the polynomial-quotient model to the coordinate
model of a quadratic algebra. -/
@[expose]
def fromAdjoinRoot (a b : R) :
    AdjoinRoot (definingPolynomial a b) →ₐ[R] QuadraticAlgebra R a b :=
  AdjoinRoot.liftAlgHom (definingPolynomial a b)
    (Algebra.ofId R (QuadraticAlgebra R a b)) omega (by
      simp [definingPolynomial, omega_pow_two_eq_add, Algebra.smul_def]
      ring)

/-- The quotient-to-coordinate map sends the adjoined root to `omega`. -/
@[simp]
theorem fromAdjoinRoot_root (a b : R) :
    fromAdjoinRoot a b (AdjoinRoot.root (definingPolynomial a b)) = omega := by
  simp [fromAdjoinRoot]

/-- The canonical map from the coordinate model of a quadratic algebra to its
polynomial-quotient model. -/
@[expose]
def toAdjoinRoot (a b : R) :
    QuadraticAlgebra R a b →ₐ[R] AdjoinRoot (definingPolynomial a b) :=
  QuadraticAlgebra.lift ⟨AdjoinRoot.root (definingPolynomial a b), by
    have h :
        AdjoinRoot.mk (definingPolynomial a b) (X ^ 2) =
          AdjoinRoot.mk (definingPolynomial a b) (C b * X + C a) :=
      sub_eq_zero.mp (by
        rw [← map_sub]
        exact AdjoinRoot.mk_self)
    have h' :
        AdjoinRoot.root (definingPolynomial a b) ^ 2 =
          algebraMap R (AdjoinRoot (definingPolynomial a b)) b *
              AdjoinRoot.root (definingPolynomial a b) +
            algebraMap R (AdjoinRoot (definingPolynomial a b)) a := by
      simpa only [map_pow, map_add, map_mul, AdjoinRoot.mk_X,
        AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq] using h
    simpa [Algebra.smul_def, pow_two, add_comm] using h'⟩

/-- The coordinate-to-quotient map sends `omega` to the adjoined root. -/
@[simp]
theorem toAdjoinRoot_omega (a b : R) :
    toAdjoinRoot a b omega = AdjoinRoot.root (definingPolynomial a b) := by
  simp [toAdjoinRoot]

/-- The canonical algebra equivalence between the coordinate and
polynomial-quotient models of a quadratic algebra. -/
@[expose]
def equivAdjoinRoot (a b : R) :
    QuadraticAlgebra R a b ≃ₐ[R] AdjoinRoot (definingPolynomial a b) :=
  AlgEquiv.ofAlgHom (toAdjoinRoot a b) (fromAdjoinRoot a b)
    (by
      apply AdjoinRoot.algHom_ext
      simp)
    (by
      apply QuadraticAlgebra.algHom_ext
      simp)

/-- The canonical equivalence identifies `omega` with the quotient's root. -/
@[simp]
theorem equivAdjoinRoot_apply_omega (a b : R) :
    equivAdjoinRoot a b omega = AdjoinRoot.root (definingPolynomial a b) := by
  simp [equivAdjoinRoot]

/-- The inverse canonical equivalence identifies the quotient's root with `omega`. -/
@[simp]
theorem equivAdjoinRoot_symm_apply_root (a b : R) :
    (equivAdjoinRoot a b).symm (AdjoinRoot.root (definingPolynomial a b)) = omega := by
  simp [equivAdjoinRoot]

end QuadraticAlgebra
