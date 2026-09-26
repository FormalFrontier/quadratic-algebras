/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import QuadraticAlgebras.FractionRing

/-!
# README scalar-extension example

Scalar extension over arbitrary commutative rings and reduction of the
defining polynomial.

This named private client is the corresponding README Lean block. It adds no public API.
-/

open scoped TensorProduct

universe u v

private theorem scalarExtensionGenerator
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (a b : R) :
    QuadraticAlgebra.baseChangeEquiv S a b
      (1 ⊗ₜ[R] (QuadraticAlgebra.omega : QuadraticAlgebra R a b)) =
        (QuadraticAlgebra.omega :
          QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  QuadraticAlgebra.baseChangeEquiv_omega S a b

private theorem definingPolynomialReduction (R : Type u) [CommRing R] (a b : R) :
    QuadraticAlgebra.definingPolynomial a b =
      Polynomial.X ^ 2 - (Polynomial.C b * Polynomial.X + Polynomial.C a) :=
  rfl
