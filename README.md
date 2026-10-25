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
guide to the newer real-closed declarations; the [binding guide](docs/README.md)
also describes the later complex quotient interface and module imports.

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
that a quadratic algebra with squarefree radicand over a unique factorization
domain is integrally closed in its total quotient ring when `2` is invertible,
even if the quadratic algebra has zero divisors. Conversely, for a domain
quadratic algebra, a nonzero nonunit square divisor of the radicand gives an
explicit integral fraction outside the quadratic algebra; in particular, a
domain quadratic algebra over a unique factorization domain is not integrally
closed when its
radicand is not squarefree. Together, these results give the exact criterion:
a domain quadratic algebra over a unique factorization domain, with `2`
invertible, is integrally closed if and only if its radicand is squarefree.

Here `IsIntegrallyClosed` uses Mathlib's total quotient ring, not necessarily a
fraction field. The forward theorem applies, for example, to `A = ℚ`, `f = 1`,
where the quadratic algebra is isomorphic to `ℚ × ℚ`. The reverse obstruction
and the if-and-only-if criterion retain their quadratic-domain hypothesis.
For `A = ℚ`, `f = 0`, the dual numbers have only units as regular elements,
so they are integrally closed in this total-quotient sense although `0` is not
squarefree. Thus the converse cannot simply drop the domain hypothesis.

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

### Complex coordinates and real polynomial quotients

The [complex coordinate equivalence](QuadraticAlgebras/RealComplexAdjoinRoot.lean)
identifies `QuadraticAlgebra ℝ (-1) 0` with `ℂ` as real algebras, sending
`omega` to `Complex.I` and exposing both coordinate formulas. For an
irreducible `p : ℝ[X]` of degree two and any specified complex root `z`, the
same module identifies `AdjoinRoot p` with `ℂ` by evaluation at `z`: the
image of `AdjoinRoot.mk p g` is `g.eval₂ (algebraMap ℝ ℂ) z` for every `g`.
For any irreducible nonlinear real polynomial it also provides a witness-free
equivalence using a selected complex root, without choosing a sign or
requiring monicity, a discriminant witness, or a root from the caller. The
[Gaussian clients](QuadraticAlgebrasTest/RealComplexAdjoinRoot.lean) exercise
both `±Complex.I`, a nonmonic scalar multiple, arbitrary quotient classes and
the variable class in the ideal quotient. This is an algebraic presentation;
it does not supply maximality, scheme residue fields or topology.

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
`QuadraticAlgebras` reexports all seventeen production leaves. Most names are in
the `QuadraticAlgebra` namespace; the other namespaces are identified in the table.

| Leaf | Main interface and boundary |
| --- | --- |
| `AdjoinRoot` | `definingPolynomial`, `equivAdjoinRoot`, and generator equations over any commutative ring. The convention is `omega ^ 2 = a + b * omega`. |
| [`RealClosedCoordinates`](QuadraticAlgebras/RealClosedCoordinates.lean) | [Real-closed negative-discriminant witness](docs/API.md#qa-real-closed-witness); [signed generator equivalence](docs/API.md#qa-chosen-coordinates) over a field with nonzero two and a supplied nonzero witness; [monic degree-two quotient coordinates](docs/API.md#qa-chosen-quotient). |
| [`RealClosedClosure`](QuadraticAlgebras/RealClosedClosure.lean) | `IsAlgClosed (QuadraticAlgebra R (-1) 0)` and `IsRealClosed.irreducible_natDegree_le_two` for `[Field R] [IsRealClosed R]`; the square-root and odd-extension helpers are also public. |
| [`RealClosedAdjoinRoot`](QuadraticAlgebras/RealClosedAdjoinRoot.lean) | `adjoinRootEquivOfRoot` for a specified root of an irreducible quadratic over any field, and `adjoinRootEquivOfIrreducible` for nonlinear polynomials over a real-closed field without a supplied root; generator and polynomial-class evaluation laws. |
| [`RealComplexAdjoinRoot`](QuadraticAlgebras/RealComplexAdjoinRoot.lean) | `realComplexEquiv` identifies `QuadraticAlgebra ℝ (-1) 0` with `ℂ` by real and imaginary coordinates. For irreducible real quadratics, `adjoinRootComplexEquivOfRoot` evaluates every quotient class at a supplied complex root; for irreducible nonlinear real polynomials, `adjoinRootComplexEquivOfIrreducible` uses a selected root without monicity or a caller-supplied root. |
| `FractionRing` | `baseChangeHom`, `baseChangeEquiv`, `fractionRingEquivTensor`, `fractionRingEquivBaseChange`, `fractionRingEquivAdjoinRoot`; their generator and algebra-map lemmas retain arbitrary commutative rings. |
| `Squarefree` | `IsFractionRing.isInteger_of_sq_mul_squarefree`: denominator descent for a UFD/domain and a chosen fraction field. `IsLocalization.IsInteger` means membership in the image of the base ring, not merely `IsIntegral`. |
| `Integral` | `starAlgEquiv`, `isIntegral_star`, and trace/norm membership lemmas over an integrally closed base with a fraction-ring structure. The quadratic algebra need not be a domain. |
| `IntegralClosure` | `isIntegrallyClosed_of_squarefree` in the total quotient ring over a UFD with two invertible; the quadratic algebra need not be a domain. |
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

See the [examples and proof-idea guide](docs/Examples.md#proof-ideas) for
the arguments behind the localization, integral-closure, diagonal and
class-number results.

## Build

Fetch the pinned mathlib cache before every build in a fresh checkout:

```sh
lake exe cache get
lake build
```

The project uses Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`.

The named downstream test-library target compiles the direct-leaf and
aggregate-only clients, the four stored README modules and the
chosen-coordinate, real-closed closure, irreducible-quotient and real/complex
quotient examples.
All twenty-nine modules (seventeen production leaves, the aggregate root and
eleven test/example modules)
are included in the default build. The coordinate test leaf has one public
`gaussianWitness` and fourteen private named clients; the real-closed model
and closure client leaves expose their boundary and comparison theorems. The
irreducible-quotient test leaf exercises both specified roots, a nonmonic
quadratic and the witness-free equivalence. The real/complex quotient test leaf
uses the independent real model's Gaussian and boundary results, and exercises
the coordinate and quotient maps with both complex roots, a nonmonic input and
the ideal-quotient variable. The six older test/example modules
remain private-only:

```sh
lake build QuadraticAlgebrasTest
lake build
```

To treat warnings as errors during a check, use `lake --wfail build` or
`lake --wfail build QuadraticAlgebrasTest` after fetching the pinned cache.

## Using the library

Add the package to your `lakefile.toml`:

```toml
[[require]]
name = "quadratic-algebras"
git = "https://github.com/FormalFrontier/quadratic-algebras.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves a release when you first
add or update the dependency; `lake-manifest.json` keeps that commit until you
update again. Replace `main` with a full commit from the release history to pin
one explicitly. When combining deliverables, choose releases with a common
Mathlib revision: Lake resolves one version of each package per build.

Use the Lean toolchain recorded by the selected release. Libraries combined
in one project must agree on that toolchain as well as their Mathlib revision;
a newer Mathlib revision is not automatically compatible.

The aggregate import gives, for example, the discriminant and class number
of the field generated by a square root of minus five:

```lean
module
import QuadraticAlgebras

private theorem negativeFiveDiscriminantAndClassNumber :
    NumberField.discr QuadraticAlgebra.SqrtNegFiveField = -20 ∧
      NumberField.classNumber QuadraticAlgebra.SqrtNegFiveField = 2 :=
  ⟨QuadraticAlgebra.discr_sqrtNegFiveField,
    QuadraticAlgebra.classNumber_sqrtNegFiveField⟩
```

The [examples guide](docs/Examples.md#examples) gives the four standalone,
named examples stored in the test library, from generic scalar extension and
integral closure to diagonal squarefreeness and the class number of `ℚ(√-5)`.

## Generated documentation and checks

The [API reference](docs/API.md) preserves all 92 historical native display
signatures, including five instances, from the [previously published native
reference](https://github.com/FormalFrontier/quadratic-algebras/blob/e5ac018d29892d2a8612f4ca8d4babaabb9c4d15/docs/API.md).
It separately describes three source-derived supplements: all seven public
chosen-coordinate declarations and the real-closed closure and
irreducible-quotient interfaces. The current scalar-extension and integral-closure
notes are also source-derived; the historical forward integral-closure signature
retains a now-unneeded quadratic-domain instance. These descriptions are not new
native-generated signatures or a complete generated-current inventory. The
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
  2025 draft): §3.2 Exercise 3.2.B motivates the complex quotient;
  Exercise 5.4.H supplies the trace/norm, denominator and
  repeated-square proof route for integral closure; 5.4.I(a) motivates the
  integer criterion, 5.4.I(b) a diagonal prerequisite, 5.4.K the minus-five
  example and 5.4.N the binary diagonal case. The reusable generalizations
  here are not claimed as complete exercise formalizations.
- [Mathlib at the pinned revision `83abb3e776bdefcbc447a1e44d0debe4010039e5`](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5)
  supplies the imported formalizations, including
  [`Algebra.QuadraticAlgebra.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/QuadraticAlgebra/Basic.lean),
  [`Basic.Complex.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Basic/Complex/Basic.lean),
  [`Algebra.QuadraticAlgebra.Discriminant`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean)
  (`QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr`),
  [`FieldTheory.IsRealClosed.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/FieldTheory/IsRealClosed/Basic.lean)
  (`IsRealClosed.isSquare_neg_of_not_isSquare`),
  [`RingTheory.AdjoinRoot`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/AdjoinRoot.lean),
  [`RingTheory.Localization.BaseChange`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/Localization/BaseChange.lean),
  [`RingTheory.IntegralClosure.IntegrallyClosed`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean),
  [`RingTheory.MvPolynomial.IrreducibleQuadratic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/MvPolynomial/IrreducibleQuadratic.lean),
  [`RingTheory.DedekindDomain.Basic`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/DedekindDomain/Basic.lean),
  and [`NumberTheory.NumberField.ClassNumber`](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/NumberTheory/NumberField/ClassNumber.lean).
  The latter module, by Anne Baanen, Riccardo Brasca and Xavier Roblot,
  supplies the ideal-class representative bound used for `ℚ(√-5)`; this
  library separately computes its discriminant, bound and norm-two ideal.
