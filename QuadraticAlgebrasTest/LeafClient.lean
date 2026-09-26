/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import QuadraticAlgebras.AdjoinRoot
import QuadraticAlgebras.FractionRing
import QuadraticAlgebras.Squarefree
import QuadraticAlgebras.Integral
import QuadraticAlgebras.IntegralClosure
import QuadraticAlgebras.IntegralClosureInt
import QuadraticAlgebras.RepeatedSquare
import QuadraticAlgebras.IntegralClosureCriterion
import QuadraticAlgebras.Dedekind
import QuadraticAlgebras.Diagonal
import QuadraticAlgebras.SqrtNegFive
import QuadraticAlgebras.NumberField
import QuadraticAlgebras.ClassNumberNegFive

/-!
# Direct-leaf downstream checks

All declarations are named and private: these tests use public imports without
adding anything to the mathematical library's exported interface.
-/

noncomputable section

open scoped TensorProduct

namespace QuadraticAlgebrasTest

universe u v

private def polynomialEquivalence (R : Type u) [CommRing R] (a b : R) :
    QuadraticAlgebra R a b ≃ₐ[R]
      AdjoinRoot (QuadraticAlgebra.definingPolynomial a b) :=
  QuadraticAlgebra.equivAdjoinRoot a b

private theorem polynomialGenerator (R : Type u) [CommRing R] (a b : R) :
    polynomialEquivalence R a b (QuadraticAlgebra.omega : QuadraticAlgebra R a b) =
      AdjoinRoot.root (QuadraticAlgebra.definingPolynomial a b) := by
  simp [polynomialEquivalence]

private theorem zeroRingGenerator :
    QuadraticAlgebra.equivAdjoinRoot (0 : ZMod 1) (0 : ZMod 1)
        (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod 1) 0 0) =
      AdjoinRoot.root (QuadraticAlgebra.definingPolynomial (0 : ZMod 1) 0) := by
  simp

private def scalarExtension (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (a b : R) :
    S ⊗[R] QuadraticAlgebra R a b ≃ₐ[S]
      QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) :=
  QuadraticAlgebra.baseChangeEquiv S a b

private theorem tensorGenerator (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (a b : R) :
    scalarExtension R S a b
        (1 ⊗ₜ[R] (QuadraticAlgebra.omega : QuadraticAlgebra R a b)) =
      (QuadraticAlgebra.omega :
        QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
  simpa [scalarExtension] using QuadraticAlgebra.baseChangeEquiv_omega S a b

private theorem fractionCoordinates (R : Type u) [CommRing R] (a b : R)
    (x : QuadraticAlgebra R a b) :
    QuadraticAlgebra.fractionRingEquivBaseChange a b
        (algebraMap (QuadraticAlgebra R a b)
          (FractionRing (QuadraticAlgebra R a b)) x) =
      QuadraticAlgebra.mk (algebraMap R (FractionRing R) x.re)
        (algebraMap R (FractionRing R) x.im) := by
  simp

private theorem fractionAdjoinRootGenerator (R : Type u) [CommRing R] (a b : R) :
    QuadraticAlgebra.fractionRingEquivAdjoinRoot a b
        (algebraMap (QuadraticAlgebra R a b)
          (FractionRing (QuadraticAlgebra R a b)) QuadraticAlgebra.omega) =
      AdjoinRoot.root
        (QuadraticAlgebra.definingPolynomial
          (algebraMap R (FractionRing R) a)
          (algebraMap R (FractionRing R) b)) := by
  simp

private theorem conjugateIntegral (R : Type u) (K : Type v)
    [CommRing R] [CommRing K] [Algebra R K] (a b : K)
    (x : QuadraticAlgebra K a b) (hx : IsIntegral R x) :
    IsIntegral R (star x) :=
  QuadraticAlgebra.isIntegral_star hx

private theorem traceAndNormDescend (R : Type u) (K : Type v)
    [CommRing R] [IsIntegrallyClosed R] [CommRing K]
    [Algebra R K] [IsFractionRing R K] (a b : K)
    (x : QuadraticAlgebra K a b) (hx : IsIntegral R x) :
    IsLocalization.IsInteger R (QuadraticAlgebra.trace x) ∧
      IsLocalization.IsInteger R (QuadraticAlgebra.norm x) :=
  ⟨QuadraticAlgebra.isInteger_trace_of_isIntegral hx,
    QuadraticAlgebra.isInteger_norm_of_isIntegral hx⟩

private theorem squarefreeDenominator (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) (hf : Squarefree f) (x : K)
    (hx : IsLocalization.IsInteger R (x ^ 2 * algebraMap R K f)) :
    IsLocalization.IsInteger R x :=
  IsFractionRing.isInteger_of_sq_mul_squarefree hf hx

private theorem squarefreeClosure (R : Type u)
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Invertible (2 : R)] (f : R) (hf : Squarefree f)
    [IsDomain (QuadraticAlgebra R f 0)] :
    IsIntegrallyClosed (QuadraticAlgebra R f 0) :=
  QuadraticAlgebra.isIntegrallyClosed_of_squarefree hf

private theorem repeatedSquareObstruction (R : Type u)
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (f : R) [IsDomain (QuadraticAlgebra R f 0)]
    (hf : ¬ Squarefree f) :
    ¬ IsIntegrallyClosed (QuadraticAlgebra R f 0) :=
  QuadraticAlgebra.not_isIntegrallyClosed_of_not_squarefree hf

private theorem squarefreeClosureCriterion (R : Type u)
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Invertible (2 : R)] (f : R) [IsDomain (QuadraticAlgebra R f 0)] :
    IsIntegrallyClosed (QuadraticAlgebra R f 0) ↔ Squarefree f :=
  QuadraticAlgebra.isIntegrallyClosed_iff_squarefree

private theorem integerSpecialization (f : ℤ)
    (hmod : f % 4 = 2 ∨ f % 4 = 3) (hf : Squarefree f) :
    IsDomain (QuadraticAlgebra ℤ f 0) ∧
      IsIntegrallyClosed (QuadraticAlgebra ℤ f 0) :=
  ⟨QuadraticAlgebra.isDomain_int_of_emod_four hmod,
    QuadraticAlgebra.isIntegrallyClosed_int_of_squarefree_of_emod_four hf hmod⟩

private theorem dedekindBridge (R : Type u) [CommRing R]
    [IsDedekindDomain R] (a b : R)
    [IsDomain (QuadraticAlgebra R a b)]
    [IsIntegrallyClosed (QuadraticAlgebra R a b)] :
    IsDedekindDomain (QuadraticAlgebra R a b) :=
  QuadraticAlgebra.isDedekindDomain_of_isIntegrallyClosed

private theorem diagonalCoefficients (ι : Type u) (R : Type v)
    [CommRing R] (c : ι →₀ R) (index : ι) :
    (MvPolynomial.sumSMulXSq c).coeff (Finsupp.single index 2) = c index ∧
      (MvPolynomial.sumSMulXSq c).IsHomogeneous 2 :=
  ⟨MvPolynomial.coeff_sumSMulXSq c index,
    MvPolynomial.isHomogeneous_sumSMulXSq c⟩

private theorem diagonalDerivative (ι : Type u) (R : Type v)
    [CommRing R] (c : ι →₀ R) (index : ι) :
    MvPolynomial.pderiv index (MvPolynomial.sumSMulXSq c) =
      MvPolynomial.C (2 * c index) * MvPolynomial.X index :=
  MvPolynomial.pderiv_sumSMulXSq c index

private theorem ternaryIrreducible (ι : Type u) (K : Type v)
    [Field K] [NeZero (2 : K)] (c : ι →₀ K)
    (hc : 3 ≤ c.support.card) :
    Irreducible (MvPolynomial.sumSMulXSq c) :=
  MvPolynomial.irreducible_sumSMulXSq c hc

private theorem binaryIrreducible (ι : Type u) (K : Type v)
    [Field K] [NeZero (2 : K)] (i j : ι) (hij : i ≠ j)
    (a b : K) (ha : a ≠ 0) (hnsq : ¬ IsSquare (-b / a)) :
    Irreducible (MvPolynomial.C a * MvPolynomial.X i ^ 2 +
      MvPolynomial.C b * MvPolynomial.X j ^ 2) :=
  MvPolynomial.irreducible_C_mul_X_sq_add_C_mul_X_sq_of_not_isSquare hij ha hnsq

private theorem binarySquarefree (ι : Type u) (K : Type v)
    [Field K] [NeZero (2 : K)] (c : ι →₀ K)
    (hc : c.support.Nontrivial) :
    Squarefree (MvPolynomial.sumSMulXSq c) :=
  MvPolynomial.squarefree_sumSMulXSq c hc

private theorem negativeFiveNotUFD :
    ¬ UniqueFactorizationMonoid (QuadraticAlgebra ℤ (-5 : ℤ) 0) :=
  QuadraticAlgebra.not_uniqueFactorizationMonoid_int_negFive

private def coordinateTransport (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] (equiv : R ≃+* S) (a b : R) :
    QuadraticAlgebra R a b ≃+*
      QuadraticAlgebra S (equiv a) (equiv b) :=
  QuadraticAlgebra.mapCoeffsEquiv equiv a b

private theorem coordinateTransportReduction (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] (equiv : R ≃+* S) (a b : R)
    (x : QuadraticAlgebra R a b) :
    (coordinateTransport R S equiv a b x).re = equiv x.re := by
  rfl

private theorem numberFieldFromDomain (a b : ℤ)
    [IsDomain (QuadraticAlgebra ℤ a b)] :
    ∃ _ : NumberField (FractionRing (QuadraticAlgebra ℤ a b)), True :=
  ⟨inferInstance, trivial⟩

private theorem negativeFiveNumberField :
    ∃ _ : NumberField QuadraticAlgebra.SqrtNegFiveField, True :=
  ⟨inferInstance, trivial⟩

private theorem negativeFiveTotallyComplex :
    ∃ _ : NumberField.IsTotallyComplex QuadraticAlgebra.SqrtNegFiveField, True :=
  ⟨inferInstance, trivial⟩

private theorem negativeFiveDegreeAndDiscriminant :
    Module.finrank ℚ QuadraticAlgebra.SqrtNegFiveField = 2 ∧
      NumberField.discr QuadraticAlgebra.SqrtNegFiveField = -20 :=
  ⟨QuadraticAlgebra.finrank_sqrtNegFiveField,
    QuadraticAlgebra.discr_sqrtNegFiveField⟩

private theorem reductionOnGenerator :
    QuadraticAlgebra.sqrtNegFiveModTwo
      (QuadraticAlgebra.omega : QuadraticAlgebra.SqrtNegFiveOrder) = 1 := by
  rfl

private theorem reductionKernelAndQuotient :
    QuadraticAlgebra.sqrtNegFiveIdealTwo =
        RingHom.ker QuadraticAlgebra.sqrtNegFiveModTwo ∧
      Nonempty (QuadraticAlgebra.SqrtNegFiveOrder ⧸
        QuadraticAlgebra.sqrtNegFiveIdealTwo ≃+* ZMod 2) :=
  ⟨rfl, ⟨QuadraticAlgebra.quotientSqrtNegFiveIdealTwoEquiv⟩⟩

private theorem ringOfIntegersClassification
    (classRepresentative : ClassGroup QuadraticAlgebra.SqrtNegFiveRingOfIntegers) :
    classRepresentative = 1 ∨
      classRepresentative = ClassGroup.mk0
        QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwoNonzero :=
  QuadraticAlgebra.classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo
    classRepresentative

private theorem negativeFiveClassNumber :
    NumberField.classNumber QuadraticAlgebra.SqrtNegFiveField = 2 :=
  QuadraticAlgebra.classNumber_sqrtNegFiveField

end QuadraticAlgebrasTest
