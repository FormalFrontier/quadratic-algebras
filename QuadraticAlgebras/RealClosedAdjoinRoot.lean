/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import QuadraticAlgebras.RealClosedClosure

/-!
# Irreducible polynomial quotients over real-closed fields

An irreducible quadratic over a field with a specified root in the quadratic
algebra has an algebra equivalence from its `AdjoinRoot` quotient, with
evaluation at that root on every polynomial class. Over a real-closed field,
every irreducible nonlinear polynomial has degree two and a root in the
canonical quadratic field. Choosing such a root gives a noncanonical
witness-free interface; opposite choices need not give the same map.

## References

* The Artin–Schreier characterization of real-closed fields underlies the
  irreducible degree bound and algebraic closure of the quadratic field.
* Mathlib's `RingTheory.AdjoinRoot` provides `AdjoinRoot.liftAlgHom` and its
  evaluation laws and power basis. Injectivity of a homomorphism out of the
  irreducible quotient field, together with equality of the two finranks,
  gives bijectivity. `FieldTheory.IsRealClosed.Basic` supplies the real-closed
  class. The degree bound and algebraic-closure instance are in
  `QuadraticAlgebras.RealClosedClosure`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option linter.style.header false

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [Field R]

/-- An irreducible degree-two polynomial and a specified root in the quadratic
algebra determine an algebra equivalence over any base field. The image of the
adjoined root is exactly the specified root; no sign or normalization is
imposed. -/
noncomputable def adjoinRootEquivOfRoot (p : R[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : QuadraticAlgebra R (-1) 0)
    (hz : p.aeval z = 0) :
    AdjoinRoot p ≃ₐ[R] QuadraticAlgebra R (-1) 0 :=
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom p (Algebra.ofId R _) z (by
      simpa only [Polynomial.aeval_def, Algebra.toRingHom_ofId] using hz)) (by
      let lift := AdjoinRoot.liftAlgHom p (Algebra.ofId R _) z (by
        simpa only [Polynomial.aeval_def, Algebra.toRingHom_ofId] using hz)
      change Function.Bijective lift
      have : Fact (Irreducible p) := ⟨hp⟩
      have : FiniteDimensional R (AdjoinRoot p) :=
        Module.Finite.of_basis (AdjoinRoot.powerBasis hp.ne_zero).basis
      have hfinrank : Module.finrank R (AdjoinRoot p) =
          Module.finrank R (QuadraticAlgebra R (-1) 0) := by
        calc
          _ = p.natDegree := finrank_quotient_span_eq_natDegree
          _ = 2 := hdeg
          _ = _ := (QuadraticAlgebra.finrank_eq_two (-1 : R) 0).symm
      have hinj : Function.Injective lift := RingHom.injective lift.toRingHom
      have hsurj : Function.Surjective lift.toLinearMap :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank
          (f := lift.toLinearMap)).mp (fun x y hxy =>
            hinj (by simpa only [AlgHom.toLinearMap_apply] using hxy))
      exact ⟨hinj, fun y => by
        obtain ⟨x, hx⟩ := hsurj y
        exact ⟨x, by simpa only [AlgHom.toLinearMap_apply] using hx⟩⟩)

/-- The chosen-root equivalence takes the adjoined root to the chosen root. -/
@[simp]
theorem adjoinRootEquivOfRoot_root (p : R[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : QuadraticAlgebra R (-1) 0)
    (hz : p.aeval z = 0) :
    adjoinRootEquivOfRoot p hp hdeg z hz (AdjoinRoot.root p) = z := by
  simp only [adjoinRootEquivOfRoot, AlgEquiv.ofBijective_apply,
    AdjoinRoot.liftAlgHom_root]

/-- The chosen-root equivalence evaluates every polynomial representative at
the chosen root. -/
theorem adjoinRootEquivOfRoot_mk (p : R[X]) (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (z : QuadraticAlgebra R (-1) 0)
    (hz : p.aeval z = 0) (g : R[X]) :
    adjoinRootEquivOfRoot p hp hdeg z hz (AdjoinRoot.mk p g) =
      g.eval₂ (algebraMap R (QuadraticAlgebra R (-1) 0)) z := by
  calc
    _ = adjoinRootEquivOfRoot p hp hdeg z hz (aeval (AdjoinRoot.root p) g) := by
      rw [AdjoinRoot.aeval_eq]
    _ = g.eval₂ (algebraMap R (QuadraticAlgebra R (-1) 0))
          (adjoinRootEquivOfRoot p hp hdeg z hz (AdjoinRoot.root p)) := by
      rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]
    _ = _ := by rw [adjoinRootEquivOfRoot_root]

variable [IsRealClosed R]

/-- A noncanonical root of an irreducible polynomial in the algebraically
closed quadratic extension of a real-closed field. -/
noncomputable def rootOfIrreducible (p : R[X]) (hp : Irreducible p) :
    QuadraticAlgebra R (-1) 0 :=
  Classical.choose
    (IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne')

/-- The chosen root satisfies the defining polynomial. -/
theorem rootOfIrreducible_aeval (p : R[X]) (hp : Irreducible p) :
    p.aeval (rootOfIrreducible p hp) = 0 :=
  Classical.choose_spec
    (IsAlgClosed.exists_aeval_eq_zero _ p (degree_pos_of_irreducible hp).ne')

/-- The quotient by any irreducible nonlinear polynomial over a real-closed
field is algebra-equivalent to its canonical quadratic field. The choice of
root fixes the map but is not part of the caller's hypotheses. -/
noncomputable def adjoinRootEquivOfIrreducible (p : R[X]) (hp : Irreducible p)
    (hdeg : 1 < p.natDegree) :
    AdjoinRoot p ≃ₐ[R] QuadraticAlgebra R (-1) 0 :=
  adjoinRootEquivOfRoot p hp
    (Nat.le_antisymm (IsRealClosed.irreducible_natDegree_le_two hp)
      (Nat.succ_le_of_lt hdeg)) (rootOfIrreducible p hp)
    (rootOfIrreducible_aeval p hp)

/-- The witness-free equivalence sends the adjoined root to its selected root. -/
@[simp]
theorem adjoinRootEquivOfIrreducible_root (p : R[X]) (hp : Irreducible p)
    (hdeg : 1 < p.natDegree) :
    adjoinRootEquivOfIrreducible p hp hdeg (AdjoinRoot.root p) =
      rootOfIrreducible p hp :=
  adjoinRootEquivOfRoot_root p hp _ _ _

/-- The witness-free equivalence evaluates every polynomial class at its
selected root. -/
theorem adjoinRootEquivOfIrreducible_mk (p : R[X]) (hp : Irreducible p)
    (hdeg : 1 < p.natDegree) (g : R[X]) :
    adjoinRootEquivOfIrreducible p hp hdeg (AdjoinRoot.mk p g) =
      g.eval₂ (algebraMap R (QuadraticAlgebra R (-1) 0))
        (rootOfIrreducible p hp) :=
  adjoinRootEquivOfRoot_mk p hp _ _ _ g

end QuadraticAlgebra
