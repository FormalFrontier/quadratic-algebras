<!-- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -->

# quadratic-algebras

Reusable Lean theory of quadratic algebras, conjugation, integral closure, and
squarefree radicands.

Licensed under the Apache License, Version 2.0 (see [LICENSE](LICENSE)).
**Authors: Formal Frontier Agents.** The project uses AI agents, Lean and
separately authored Mathlib APIs; see [attribution](#attribution-and-scope).

<a id="mathematical-scope"></a>

## Headline results

The results below extend mathlib's quadratic-algebra, polynomial, localization
and number-field infrastructure. They provide changes of presentation,
integral-closure tests and explicit arithmetic examples; the imported
infrastructure is not a new contribution of this library. The
[API reference](docs/API.md) gives the historical native signatures and a
guide to the newer real-closed declarations and module imports.

### Presentations, scalar extension and integral closure

The library connects mathlib's coordinate model `QuadraticAlgebra R a b` with
the polynomial quotient `AdjoinRoot (X ^ 2 - C b * X - C a)`. It also proves
that scalar extension commutes with quadratic algebras and canonically
identifies their total fraction rings with base change to `FractionRing R`.
These results allow zero divisors and the zero ring: a total fraction ring is
not being asserted to be a field. The library also proves
the squarefree denominator lemma for arbitrary fraction fields of unique
factorization domains: if `f` is squarefree and `x² f` lies in the base ring,
then `x` is already in the base ring. It also shows
that the trace and norm of an integral quadratic element over the fraction
field of an integrally closed ring belong to the base ring, without assuming
that the quadratic algebra is a domain. Combining these ingredients, it proves
that a domain quadratic algebra with squarefree radicand over a unique
factorization domain is integrally closed when `2` is invertible. Conversely,
a nonzero nonunit square divisor of the radicand gives an explicit integral
fraction outside the quadratic algebra; in particular, a domain quadratic
algebra over a unique factorization domain is not integrally closed when its
radicand is not squarefree. Together, these results give the exact criterion:
a domain quadratic algebra over a unique factorization domain, with `2`
invertible, is integrally closed if and only if its radicand is squarefree.
Over the integers, where `2` is not invertible, the library separately proves
that a quadratic algebra with squarefree radicand is integrally closed when
the radicand is congruent to `2` or `3` modulo `4`; this congruence also yields
the required domain property. This integer result does not assume that two is
invertible in the integers.

Key interfaces are the [polynomial-quotient equivalence](docs/API.md#qa-equiv-adjoin-root),
[scalar-extension and total-fraction-ring maps](QuadraticAlgebras/FractionRing.lean),
[UFD squarefree criterion](docs/API.md#qa-ufd-squarefree-criterion)
and [separate integer criterion](docs/API.md#qa-integer-integral-closure).

### Chosen coordinates for quadratic algebras

Over a field `R` with `[IsRealClosed R]`, irreducibility of
`QuadraticAlgebra.definingPolynomial a b` supplies a nonzero `d` with
`d² = -QuadraticAlgebra.discr a b`; see the
[real-closed witness](docs/API.md#qa-real-closed-witness). Separately, over
any field with `[NeZero (2 : R)]`, a *supplied* `d ≠ 0` satisfying this
square identity gives a [chosen equivalence](docs/API.md#qa-chosen-coordinates)
from `QuadraticAlgebra R a b` to `QuadraticAlgebra R (-1) 0`. Its generator
maps to `(d / 2) • omega + algebraMap R _ (b / 2)`; replacing `d` with `-d`
conjugates that image, without selecting a preferred sign or requiring
irreducibility of the supplied-witness equivalence. The
[quotient version](docs/API.md#qa-chosen-quotient) additionally assumes `p`
is monic with `p.natDegree = 2`, and evaluates *every* polynomial class
`AdjoinRoot.mk p g` at the image of the chosen root. These conditional chosen
coordinates are distinct from the earlier canonical quotient bridge over
arbitrary commutative rings; they do not choose a sign or provide an
arbitrary-degree quotient equivalence.

### Algebraic closure over a real-closed field

For any field `R` with `[IsRealClosed R]`, the canonical quadratic field
`QuadraticAlgebra R (-1) 0` is algebraically closed. No order or nonsquare
witness is supplied by the caller: semireality proves the field witness
`Fact (¬ IsSquare (-1 : R))`. Every element of this quadratic field has a
square root, and a finite normal closure with the Galois correspondence and
Sylow's theorem rules out any further finite extension. Consequently every
irreducible `p : R[X]` satisfies `p.natDegree ≤ 2`.

The independent [real model](QuadraticAlgebrasTest/RealClosedModel.lean) proves
`IsRealClosed ℝ` without importing the closure result. It exhibits irreducible
`X² + 1` at the bound and reducible `X² - 1` and `X⁴ - 1` as boundaries.
The [dependent clients](QuadraticAlgebrasTest/RealClosedClosure.lean) exercise
the square-root and cubic-root results and compare the general degree bound
with Mathlib's real-only bound. See the
[closure API](docs/API.md#qa-real-closed-closure).

### Irreducible polynomial quotients

For an arbitrary real-closed field `R`, each irreducible `p : R[X]` with
`1 < p.natDegree` has an `R`-algebra equivalence from `AdjoinRoot p` to
`QuadraticAlgebra R (-1) 0`; no monicity or discriminant witness is required.
Over any base field, the chosen-root constructor for an irreducible quadratic
specifies the image of the adjoined root and evaluates every polynomial class
at it. The witness-free constructor chooses
such a root without identifying the maps arising from different choices.
The [independent real model](QuadraticAlgebrasTest/RealClosedModel.lean) supplies
irreducible quadratic and reducible boundaries; the
[quotient clients](QuadraticAlgebrasTest/RealClosedAdjoinRoot.lean) also exercise
a nonmonic scalar multiple and both signs of the quadratic generator.

### Diagonal quadratics

The library also defines the finitely supported
diagonal multivariate quadratic `MvPolynomial.sumSMulXSq c`. Over any field
of characteristic different from two, this polynomial is squarefree when at
least two coefficients are nonzero and irreducible when at least three are
nonzero. A binary diagonal quadratic `aXᵢ² + bXⱼ²` is also irreducible when
`i ≠ j`, `a ≠ 0`, and `-b/a` is not a square. The declarations work over
arbitrary variable types and do not assume an algebraic closure or classify
quadratic forms. Coefficient, derivative and homogeneity lemmas need only a
commutative coefficient ring; the field and `NeZero (2 : k)` assumptions belong
to the irreducibility and squarefreeness results.

See the [diagonal construction](docs/API.md#qa-diagonal-sum),
[squarefreeness theorem](docs/API.md#qa-diagonal-squarefree),
[three-coefficient irreducibility theorem](docs/API.md#qa-diagonal-irreducible)
and [binary nonsquare criterion](docs/API.md#qa-binary-diagonal-irreducible).

### The order and number field generated by a square root of minus five

A domain quadratic algebra
over a Dedekind domain is also shown to be Dedekind whenever it is integrally
closed, using its finite-module and integral structures. Finally, the library
proves that the integer quadratic algebra `QuadraticAlgebra ℤ (-5) 0` is not
a unique factorization monoid: the embedded integer `2` is irreducible by the
norm form `x² + 5y²`, but is not prime because
`(1 + ω) * (1 - ω) = 6`.
The fraction field of this order is also exposed as a number field, with a
canonical identification of the order with its ring of integers. Its standard
integral basis has discriminant `-20`; the field has degree two and one complex
place. The resulting explicit Minkowski estimate shows that every ideal class
has a representative of absolute norm at most two. This does not yet classify
those ideals by itself. Reduction to `ZMod 2` defines the unique ideal of
absolute norm two; this ideal is nonprincipal, while an ideal of absolute norm
one is the unit ideal. Consequently every ideal class is either trivial or the
class of this distinguished ideal, and the class number is two.
These results are independent of the organization of any motivating source.

Entry points include [failure of unique factorization](docs/API.md#qa-minus-five-not-ufd),
the [ring-of-integers identification](docs/API.md#qa-minus-five-ring-of-integers)
and the [class-number-two theorem](docs/API.md#qa-minus-five-class-number).

## Module and API guide

All paths below have the prefix `QuadraticAlgebras.`. The root
`QuadraticAlgebras` reexports all sixteen production leaves. Most names are in
the `QuadraticAlgebra` namespace; the other namespaces are identified in the table.

| Leaf | Main interface and boundary |
| --- | --- |
| `AdjoinRoot` | `definingPolynomial`, `equivAdjoinRoot`, and generator equations over any commutative ring. The convention is `omega ^ 2 = a + b * omega`. |
| [`RealClosedCoordinates`](QuadraticAlgebras/RealClosedCoordinates.lean) | [Real-closed negative-discriminant witness](docs/API.md#qa-real-closed-witness); [signed generator equivalence](docs/API.md#qa-chosen-coordinates) over a field with nonzero two and a supplied nonzero witness; [monic degree-two quotient coordinates](docs/API.md#qa-chosen-quotient). |
| [`RealClosedClosure`](QuadraticAlgebras/RealClosedClosure.lean) | `IsAlgClosed (QuadraticAlgebra R (-1) 0)` and `IsRealClosed.irreducible_natDegree_le_two` for `[Field R] [IsRealClosed R]`; the square-root and odd-extension helpers are also public. |
| [`RealClosedAdjoinRoot`](QuadraticAlgebras/RealClosedAdjoinRoot.lean) | `adjoinRootEquivOfRoot` for a specified root of an irreducible quadratic over any field, and `adjoinRootEquivOfIrreducible` for nonlinear polynomials over a real-closed field without a supplied root; generator and polynomial-class evaluation laws. |
| `FractionRing` | `baseChangeEquiv`, `fractionRingEquivTensor`, `fractionRingEquivBaseChange`, `fractionRingEquivAdjoinRoot`; their generator and algebra-map lemmas retain arbitrary commutative rings. |
| `Squarefree` | `IsFractionRing.isInteger_of_sq_mul_squarefree`: denominator descent for a UFD/domain and a chosen fraction field. `IsLocalization.IsInteger` means membership in the image of the base ring, not merely `IsIntegral`. |
| `Integral` | `starAlgEquiv`, `isIntegral_star`, and trace/norm membership lemmas over an integrally closed base with a fraction-ring structure. The quadratic algebra need not be a domain. |
| `IntegralClosure` | `isIntegrallyClosed_of_squarefree` for a domain quadratic algebra over a UFD with two invertible. |
| `RepeatedSquare` | Explicit integral fractions outside the algebra from a nonzero nonunit square divisor. The nonsquarefree-to-prime-square step retains its nonzero-radicand hypothesis. |
| `IntegralClosureCriterion` | `isIntegrallyClosed_iff_squarefree` with the quadratic-domain, UFD and invertible-two hypotheses. |
| `IntegralClosureInt` | Domain and integral-closure theorems for integer radicands of remainder two or three modulo four; integral closure additionally needs squarefreeness. |
| `Dedekind` | `isDedekindDomain_of_isIntegrallyClosed`: an integrally closed domain quadratic algebra over a Dedekind domain is Dedekind. |
| `Diagonal` | `MvPolynomial.sumSMulXSq`, coefficient/derivative/homogeneity lemmas, and field irreducibility/squarefreeness criteria. Variable types may be infinite. |
| `SqrtNegFive` | Irreducible but nonprime two and `not_uniqueFactorizationMonoid_int_negFive`. |
| `NumberField` | Coefficient transport, `ringOfIntegersEquiv`, `SqrtNegFiveOrder`, `SqrtNegFiveField`, discriminant, degree, complex places and a norm-two bound for class representatives. |
| `ClassNumberNegFive` | The reduction map to `ZMod 2`, distinguished nonprincipal ideal of norm two, class-group classification and `classNumber_sqrtNegFiveField`. |

The number-field module installs the generic number-field instance for fraction
fields of domain integer quadratic algebras, as well as domain/integral-closure
instances for `SqrtNegFiveOrder` and total complexness for `SqrtNegFiveField`.
`ClassNumberNegFive` additionally installs the Dedekind-domain instance for this
order. In contrast, generic integral-closure criteria return typeclass proofs
for the caller to use; the library does not install them as blanket instances.

### Proof ideas

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

## Build

Fetch the pinned mathlib cache before every build in a fresh checkout:

```sh
lake exe cache get
lake build
```

The project uses Lean `v4.34.0-rc2` and mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`.

The named downstream test-library target compiles the direct-leaf and
aggregate-only clients, the four stored README modules and the
chosen-coordinate, real-closed closure and irreducible-quotient examples.
All twenty-seven modules (sixteen production leaves, the aggregate root and
ten test/example modules)
are included in the default build. The coordinate test leaf has one public
`gaussianWitness` and fourteen private named clients; the real-closed model
and closure client leaves expose their boundary and comparison theorems. The
irreducible-quotient test leaf exercises both specified roots, a nonmonic
quadratic and the witness-free equivalence. The six older test/example modules
remain private-only:

```sh
lake build QuadraticAlgebrasTest
lake build
```

To treat warnings as errors during a check, use `lake --wfail build` or
`lake --wfail build QuadraticAlgebrasTest` after fetching the pinned cache.

A historical baseline on a 23-GiB Linux runtime, after fetching the matching
dependency cache and with project outputs initially absent, totaled 92.65
seconds across twenty **sequential, warning-fatal named-module invocations**
before the coordinate modules were added. The largest
measured peak RSS of a child process was 1,838,488 KiB, not the runtime's
aggregate memory. `LAKE_JOBS=1` and `LEAN_NUM_THREADS=1` were recorded for those
commands; `LEAN_NUM_THREADS` controls each Lean runtime's workers, while the
recorded `LAKE_JOBS` does not establish default-build concurrency. That total
excludes cache preparation, native documentation generation and the separate
proof audit. It is not a cold-build timing, a portable RAM minimum, a measured
default-build concurrency limit, a measurement of the current default build
or an improvement claim.

## Using the library

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

## Generated documentation and checks

The [API reference](docs/API.md) preserves all 92 historical native display
signatures, including five instances, from the [previously published native
reference](https://github.com/FormalFrontier/quadratic-algebras/blob/e5ac018d29892d2a8612f4ca8d4babaabb9c4d15/docs/API.md).
It separately describes three source-derived supplements: all seven public
chosen-coordinate declarations and the real-closed closure and
irreducible-quotient interfaces. These supplements are not native-generated
signatures or a complete generated-current inventory. The
[historical input manifest](docs/api-manifest.json) binds the older native
analysis, not the new modules or this edited API file; the
[binding guide](docs/README.md) identifies its old hash comparison as
historical. No new native analysis or passing native `--check` is claimed.
It does not distribute a JavaScript site or external dependency documentation.

Build-checked examples, inherited native API signatures and a schema-valid metadata file
serve different purposes from semantic review and proof-integrity checks. A
public documentation inventory does not audit private or generated proof bodies.

## Attribution and scope

Atlas developed earlier mathematical Lean proofs and wrote the initial
standalone documentation and examples; another AI agent migrated the native
modules, build and downstream clients without originating those earlier proofs.
Folio contributed the headline guide, and the
[adapter lineage](docs/README.md#provenance) credits Anchor's renderer recipe.
Later contributors also wrote original mathematical Lean proofs, examples and
documentation, including new real-closed and irreducible-quotient material.
Collective author credit does not assert copyright ownership.
[`formalization.yaml`](formalization.yaml) describes the mathematical
scope, AI involvement and review status; no complete source formalization or
general classification of quadratic forms or number fields is claimed.

## References

- Emil Artin and Otto Schreier, the classical characterization of real-closed
  fields: the odd-degree extension and Sylow 2-group arguments motivate the
  quadratic-closure proof. This library works with Mathlib's unordered
  `IsRealClosed` class rather than assuming an order or algebraic closure.
- Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
  2025 draft): Exercise 5.4.H supplies the trace/norm, denominator and
  repeated-square proof route for integral closure; 5.4.I(a) motivates the
  integer criterion, 5.4.I(b) a diagonal prerequisite, 5.4.K the minus-five
  example and 5.4.N the binary diagonal case. The reusable generalizations
  here are not claimed as complete exercise formalizations.
- [Mathlib at the pinned revision `e37d88a26f3791ed5a93daa1f949af1021b8d103`](https://github.com/leanprover-community/mathlib4/tree/e37d88a26f3791ed5a93daa1f949af1021b8d103)
  supplies the imported formalizations, including
  [`Algebra.QuadraticAlgebra.Basic`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/QuadraticAlgebra/Basic.lean),
  [`Algebra.QuadraticAlgebra.Discriminant`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean)
  (`QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr`),
  [`FieldTheory.IsRealClosed.Basic`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/FieldTheory/IsRealClosed/Basic.lean)
  (`IsRealClosed.isSquare_neg_of_not_isSquare`),
  [`RingTheory.AdjoinRoot`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/AdjoinRoot.lean),
  [`RingTheory.Localization.BaseChange`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/Localization/BaseChange.lean),
  [`RingTheory.IntegralClosure.IntegrallyClosed`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean),
  [`RingTheory.MvPolynomial.IrreducibleQuadratic`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/MvPolynomial/IrreducibleQuadratic.lean),
  [`RingTheory.DedekindDomain.Basic`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/DedekindDomain/Basic.lean),
  and [`NumberTheory.NumberField.ClassNumber`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/NumberTheory/NumberField/ClassNumber.lean).
  The latter module, by Anne Baanen, Riccardo Brasca and Xavier Roblot,
  supplies the ideal-class representative bound used for `ℚ(√-5)`; this
  library separately computes its discriminant, bound and norm-two ideal.
