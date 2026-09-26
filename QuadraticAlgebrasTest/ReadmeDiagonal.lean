/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import QuadraticAlgebras.Diagonal

/-!
# README diagonal-quadratic example

Diagonal differentiation over rings and squarefreeness in characteristic
different from two.

This named private client is the corresponding README Lean block. It adds no public API.
-/

private theorem diagonalDerivative {ι R : Type*} [CommRing R]
    (c : ι →₀ R) (i : ι) :
    MvPolynomial.pderiv i (MvPolynomial.sumSMulXSq c) =
      MvPolynomial.C (2 * c i) * MvPolynomial.X i :=
  MvPolynomial.pderiv_sumSMulXSq c i

private theorem diagonalSquarefree {ι k : Type*} [Field k] [NeZero (2 : k)]
    (c : ι →₀ k) (hc : c.support.Nontrivial) :
    Squarefree (MvPolynomial.sumSMulXSq c) :=
  MvPolynomial.squarefree_sumSMulXSq c hc
