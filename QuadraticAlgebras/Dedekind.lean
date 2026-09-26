/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Dedekind quadratic algebras

This file packages the generic passage from integral closedness to the
Dedekind-domain property for a quadratic algebra over a Dedekind domain. The
quadratic algebra is finite as a module over its base, so it is Noetherian;
integrality bounds its Krull dimension by one.
-/

public section

set_option warningAsError true

namespace QuadraticAlgebra

universe u

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {a b : R}

/-- A domain quadratic algebra over a Dedekind domain is Dedekind when it is
integrally closed. -/
theorem isDedekindDomain_of_isIntegrallyClosed
    [IsDomain (QuadraticAlgebra R a b)]
    [IsIntegrallyClosed (QuadraticAlgebra R a b)] :
    IsDedekindDomain (QuadraticAlgebra R a b) := by
  let _ : IsNoetherianRing (QuadraticAlgebra R a b) :=
    IsNoetherianRing.of_finite R _
  let _ : Ring.DimensionLEOne (QuadraticAlgebra R a b) :=
    Ring.DimensionLEOne.of_isIntegral R _
  let _ : IsDedekindRing (QuadraticAlgebra R a b) := { }
  infer_instance

#print axioms isDedekindDomain_of_isIntegrallyClosed

end QuadraticAlgebra
