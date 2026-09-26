/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import QuadraticAlgebras

/-!
# Aggregate-only downstream checks

The sole import is the public library root. Named private declarations check its
exports and ordinary use without re-exporting test material.
-/

noncomputable section

namespace QuadraticAlgebrasTest

universe u v

private theorem definingPolynomialFormula (a b : ℤ) :
    QuadraticAlgebra.definingPolynomial a b =
      Polynomial.X ^ 2 -
        (Polynomial.C b * Polynomial.X + Polynomial.C a) := by
  rfl

private theorem quotientGenerator :
    QuadraticAlgebra.equivAdjoinRoot (0 : ZMod 1) (0 : ZMod 1)
        (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod 1) 0 0) =
      AdjoinRoot.root (QuadraticAlgebra.definingPolynomial (0 : ZMod 1) 0) := by
  simp

private theorem genericTensorGenerator (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (a b : R) :
    QuadraticAlgebra.baseChangeEquiv S a b
        (1 ⊗ₜ[R] (QuadraticAlgebra.omega : QuadraticAlgebra R a b)) =
      (QuadraticAlgebra.omega :
        QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  QuadraticAlgebra.baseChangeEquiv_omega S a b

private theorem genericFractionGenerator (R : Type u) [CommRing R] (a b : R) :
    QuadraticAlgebra.fractionRingEquivBaseChange a b
        (algebraMap (QuadraticAlgebra R a b)
          (FractionRing (QuadraticAlgebra R a b)) QuadraticAlgebra.omega) =
      (QuadraticAlgebra.omega :
        QuadraticAlgebra (FractionRing R)
          (algebraMap R (FractionRing R) a)
          (algebraMap R (FractionRing R) b)) :=
  QuadraticAlgebra.fractionRingEquivBaseChange_omega a b

private theorem genericClosureCriterion (R : Type u)
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Invertible (2 : R)] (f : R) [IsDomain (QuadraticAlgebra R f 0)] :
    IsIntegrallyClosed (QuadraticAlgebra R f 0) ↔ Squarefree f :=
  QuadraticAlgebra.isIntegrallyClosed_iff_squarefree

private theorem integerCongruenceClosure (f : ℤ)
    (hmod : f % 4 = 2 ∨ f % 4 = 3) (hf : Squarefree f) :
    IsIntegrallyClosed (QuadraticAlgebra ℤ f 0) :=
  QuadraticAlgebra.isIntegrallyClosed_int_of_squarefree_of_emod_four hf hmod

private theorem genericDiagonalDerivative (ι : Type u) (R : Type v)
    [CommRing R] (c : ι →₀ R) (index : ι) :
    MvPolynomial.pderiv index (MvPolynomial.sumSMulXSq c) =
      MvPolynomial.C (2 * c index) * MvPolynomial.X index :=
  MvPolynomial.pderiv_sumSMulXSq c index

private theorem diagonalDefinitionReduction (ι : Type u) (R : Type v)
    [CommRing R] :
    (MvPolynomial.sumSMulXSq : (ι →₀ R) →ₗ[R] MvPolynomial ι R) =
      Finsupp.linearCombination R (fun index => MvPolynomial.X index ^ 2) := by
  rfl

private theorem genericDiagonalSquarefree (ι : Type u) (K : Type v)
    [Field K] [NeZero (2 : K)] (c : ι →₀ K)
    (hc : c.support.Nontrivial) :
    Squarefree (MvPolynomial.sumSMulXSq c) :=
  MvPolynomial.squarefree_sumSMulXSq c hc

private theorem negativeFiveNonUFD :
    ¬ UniqueFactorizationMonoid QuadraticAlgebra.SqrtNegFiveOrder :=
  QuadraticAlgebra.not_uniqueFactorizationMonoid_int_negFive

private theorem reductionFormula :
    QuadraticAlgebra.sqrtNegFiveModTwo
        (QuadraticAlgebra.omega : QuadraticAlgebra.SqrtNegFiveOrder) = 1 ∧
      QuadraticAlgebra.sqrtNegFiveIdealTwo =
        RingHom.ker QuadraticAlgebra.sqrtNegFiveModTwo := by
  exact ⟨rfl, rfl⟩

private theorem concreteFieldAndClasses :
    Module.finrank ℚ QuadraticAlgebra.SqrtNegFiveField = 2 ∧
      NumberField.classNumber QuadraticAlgebra.SqrtNegFiveField = 2 :=
  ⟨QuadraticAlgebra.finrank_sqrtNegFiveField,
    QuadraticAlgebra.classNumber_sqrtNegFiveField⟩

end QuadraticAlgebrasTest
