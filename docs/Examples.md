<!-- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -->

# Examples and proof ideas

See the [README](../README.md#using-the-library) for package installation and
[building instructions](../README.md#build).

## Examples

The following blocks are standalone Lean modules with named private examples;
they exercise ordinary imports without extending the library's public API.
For scalar extension, no domain or nontriviality assumptions are needed:

```lean
module
import QuadraticAlgebras.FractionRing

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
```

The generic squarefree criterion retains the domain and invertible-two
assumptions. Use the distinct integer API for the modulo-four case:

```lean
module
import QuadraticAlgebras.IntegralClosureCriterion
import QuadraticAlgebras.IntegralClosureInt

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
```

Diagonal squarefreeness needs two nonzero coefficients, expressed as nontrivial
support, and characteristic different from two. The derivative formula itself
has neither requirement:

```lean
module
import QuadraticAlgebras.Diagonal

private theorem diagonalDerivative {ι R : Type*} [CommRing R]
    (c : ι →₀ R) (i : ι) :
    MvPolynomial.pderiv i (MvPolynomial.sumSMulXSq c) =
      MvPolynomial.C (2 * c i) * MvPolynomial.X i :=
  MvPolynomial.pderiv_sumSMulXSq c i

private theorem diagonalSquarefree {ι k : Type*} [Field k] [NeZero (2 : k)]
    (c : ι →₀ k) (hc : c.support.Nontrivial) :
    Squarefree (MvPolynomial.sumSMulXSq c) :=
  MvPolynomial.squarefree_sumSMulXSq c hc
```

The aggregate import also provides the concrete arithmetic conclusions:

```lean
module
import QuadraticAlgebras

private theorem negativeFiveDiscriminantAndClassNumber :
    NumberField.discr QuadraticAlgebra.SqrtNegFiveField = -20 ∧
      NumberField.classNumber QuadraticAlgebra.SqrtNegFiveField = 2 :=
  ⟨QuadraticAlgebra.discr_sqrtNegFiveField,
    QuadraticAlgebra.classNumber_sqrtNegFiveField⟩
```

`QuadraticAlgebrasTest.LeafClient` and `QuadraticAlgebrasTest.RootClient`
contain compiled, named private downstream examples, including generic
commutative-ring and zero-ring uses; they do not extend the public API.
The four blocks above are stored, with additional license/module comments, as
`ReadmeScalarExtension`, `ReadmeIntegralClosure`, `ReadmeDiagonal` and
`ReadmeNegativeFive` in the same test library. All their nonempty mathematical
code lines agree with the displayed examples.
The modules document the precise domain, characteristic, and fraction-ring
hypotheses for their respective results.

### Example source files

- [Scalar extension](../QuadraticAlgebrasTest/ReadmeScalarExtension.lean).
- [Generic and integer integral closure](../QuadraticAlgebrasTest/ReadmeIntegralClosure.lean).
- [Diagonal quadratics](../QuadraticAlgebrasTest/ReadmeDiagonal.lean).
- [Minus-five discriminant and class number](../QuadraticAlgebrasTest/ReadmeNegativeFive.lean).

## Proof ideas

For total fraction rings, multiplying a regular quadratic element by its
conjugate gives a regular scalar norm. Inverting regular scalars therefore
already inverts all regular quadratic elements. This explains why the
localization equivalences do not need a domain assumption.

For integral closure, conjugation preserves integrality, so trace and norm are
integral scalars and descend to the integrally closed base. The squarefree
denominator lemma then forces a reduced denominator to be a unit. The generic
quadratic criterion uses division by two; the integer theorem instead uses
the radicand's residue modulo four. A repeated square divisor produces the
opposite obstruction by an explicit integral fraction outside the algebra.

A nontrivial factorization of a homogeneous quadratic reduces to linear
factors. The diagonal coefficient and derivative identities rule out such a
factorization with three supported coefficients. For squarefreeness, a repeated
irreducible factor would divide the partial derivatives in two supported
variables, contradicting their distinct-variable structure when two is nonzero.

For the class number, the discriminant and signature give a Minkowski bound
strictly below three. Integral ideal norms reduce this to norms one and two.
Reduction to `ZMod 2` supplies the norm-two ideal; its uniqueness and
nonprincipality give exactly two ideal classes, while norm one gives the unit
ideal. The bound alone is not the ideal classification.
