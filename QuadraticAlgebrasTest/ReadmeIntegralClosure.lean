/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import QuadraticAlgebras.IntegralClosureCriterion
import QuadraticAlgebras.IntegralClosureInt

/-!
# README integral-closure example

The generic squarefree criterion and the separate integer congruence criterion.

This named private client is the corresponding README Lean block. It adds no public API.
-/

private theorem squarefreeCriterion (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Invertible (2 : R)] (f : R)
    [IsDomain (QuadraticAlgebra R f 0)] :
    IsIntegrallyClosed (QuadraticAlgebra R f 0) ↔ Squarefree f :=
  QuadraticAlgebra.isIntegrallyClosed_iff_squarefree

private theorem integerCriterion (f : ℤ) (hf : Squarefree f)
    (hmod : f % 4 = 2 ∨ f % 4 = 3) :
    IsDomain (QuadraticAlgebra ℤ f 0) ∧
      IsIntegrallyClosed (QuadraticAlgebra ℤ f 0) :=
  ⟨QuadraticAlgebra.isDomain_int_of_emod_four hmod,
    QuadraticAlgebra.isIntegrallyClosed_int_of_squarefree_of_emod_four hf hmod⟩
