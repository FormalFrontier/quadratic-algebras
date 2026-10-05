/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.IntegralClosure
public import QuadraticAlgebras.RepeatedSquare

/-!
# Integral closedness criterion for quadratic algebras

A domain quadratic algebra `A[ω]` with `ω² = f` over a unique factorization
domain, with `2` invertible, is integrally closed exactly when `f` is
squarefree.  This combines the squarefree integral-closedness theorem with the
repeated-square obstruction.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft), Exercise 5.4.H, supplies the trace/norm, reduced-denominator
  and repeated-square proof route. The criterion here makes its UFD, domain
  and invertibility hypotheses explicit.
-/

public section

set_option warningAsError true

noncomputable section

namespace QuadraticAlgebra

universe u

variable {A : Type u} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A] [Invertible (2 : A)]
  {f : A}

/-- A domain quadratic algebra over a UFD, with `2` invertible, is integrally
closed if and only if its radicand is squarefree. Both directions follow the
proof route in Vakil, *The Rising Sea*, Exercise 5.4.H. -/
theorem isIntegrallyClosed_iff_squarefree
    [IsDomain (QuadraticAlgebra A f 0)] :
    IsIntegrallyClosed (QuadraticAlgebra A f 0) ↔ Squarefree f := by
  constructor
  · intro hclosed
    by_contra hf
    exact not_isIntegrallyClosed_of_not_squarefree hf hclosed
  · intro hf
    exact isIntegrallyClosed_of_squarefree (A := A) (f := f) hf

end QuadraticAlgebra
