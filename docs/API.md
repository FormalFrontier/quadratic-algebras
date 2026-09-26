# Generated API reference

Complete public API of quadratic-algebras: 92 declarations in thirteen mathematical leaves.
Import `QuadraticAlgebras` for all leaves. Six test modules contain private checked
clients and README examples, not additional public API.

Signatures below are native doc-gen4 display signatures with all displayed implicit
arguments retained, not declarations with proof bodies. Short names use the source
namespace and imports; native printing can suppress type annotations on literals.
Consult the linked source for explicit types; universe parameters are arbitrary. Module documentation
is extracted verbatim from the exact source. All source links are relative to this
checkout. See [generation and provenance](README.md), [exact input manifest](api-manifest.json)
and the [mathematical overview](../README.md).

## Module `QuadraticAlgebras.AdjoinRoot`

> # Quadratic algebras as polynomial quotients
>
> This file identifies mathlib's coordinate model `QuadraticAlgebra R a b`, in
> which `omega ^ 2 = a + b * omega`, with the corresponding `AdjoinRoot` of
> `X ^ 2 - b * X - a`.

[Module source](../QuadraticAlgebras/AdjoinRoot.lean)

### QuadraticAlgebra.definingPolynomial

```lean
noncomputable def QuadraticAlgebra.definingPolynomial {R : Type u} [CommRing R] (a b : R) : Polynomial R
```

The monic polynomial defining `QuadraticAlgebra R a b`.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L32) (line 32).

### QuadraticAlgebra.definingPolynomial_monic

```lean
theorem QuadraticAlgebra.definingPolynomial_monic {R : Type u} [CommRing R] (a b : R) : (definingPolynomial a b).Monic
```

The defining quadratic is monic over every commutative ring.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L37) (line 37).

### QuadraticAlgebra.fromAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.fromAdjoinRoot {R : Type u} [CommRing R] (a b : R) : AdjoinRoot (definingPolynomial a b) →ₐ[R] QuadraticAlgebra R a b
```

The canonical map from the polynomial-quotient model to the coordinate
model of a quadratic algebra.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L42) (line 42).

### QuadraticAlgebra.fromAdjoinRoot_root

```lean
theorem QuadraticAlgebra.fromAdjoinRoot_root {R : Type u} [CommRing R] (a b : R) : (fromAdjoinRoot a b) (AdjoinRoot.root (definingPolynomial a b)) = omega
```

The quotient-to-coordinate map sends the adjoined root to `omega`.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L52) (line 52).

### QuadraticAlgebra.toAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.toAdjoinRoot {R : Type u} [CommRing R] (a b : R) : QuadraticAlgebra R a b →ₐ[R] AdjoinRoot (definingPolynomial a b)
```

The canonical map from the coordinate model of a quadratic algebra to its
polynomial-quotient model.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L58) (line 58).

### QuadraticAlgebra.toAdjoinRoot_omega

```lean
theorem QuadraticAlgebra.toAdjoinRoot_omega {R : Type u} [CommRing R] (a b : R) : (toAdjoinRoot a b) omega = AdjoinRoot.root (definingPolynomial a b)
```

The coordinate-to-quotient map sends `omega` to the adjoined root.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L79) (line 79).

### QuadraticAlgebra.equivAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.equivAdjoinRoot {R : Type u} [CommRing R] (a b : R) : QuadraticAlgebra R a b ≃ₐ[R] AdjoinRoot (definingPolynomial a b)
```

The canonical algebra equivalence between the coordinate and
polynomial-quotient models of a quadratic algebra.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L85) (line 85).

### QuadraticAlgebra.equivAdjoinRoot_apply_omega

```lean
theorem QuadraticAlgebra.equivAdjoinRoot_apply_omega {R : Type u} [CommRing R] (a b : R) : (equivAdjoinRoot a b) omega = AdjoinRoot.root (definingPolynomial a b)
```

The canonical equivalence identifies `omega` with the quotient's root.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L98) (line 98).

### QuadraticAlgebra.equivAdjoinRoot_symm_apply_root

```lean
theorem QuadraticAlgebra.equivAdjoinRoot_symm_apply_root {R : Type u} [CommRing R] (a b : R) : (equivAdjoinRoot a b).symm (AdjoinRoot.root (definingPolynomial a b)) = omega
```

The inverse canonical equivalence identifies the quotient's root with `omega`.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L104) (line 104).

## Module `QuadraticAlgebras.FractionRing`

> # Fraction rings of quadratic algebras
>
> This file identifies the total fraction ring of a quadratic algebra with its
> scalar extension to the total fraction ring of the base.  The key observation
> is that a regular quadratic element `x` becomes a scalar regular element after
> multiplication by `star x`, since `x * star x` is its norm.
>
> The results hold for arbitrary commutative rings, including rings with zero
> divisors and the zero ring.  No domain or irreducibility hypothesis is needed
> until a downstream application asks for one of the fraction rings to be a
> field.

[Module source](../QuadraticAlgebras/FractionRing.lean)

### QuadraticAlgebra.baseChangeEquiv

```lean
noncomputable def QuadraticAlgebra.baseChangeEquiv {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) : TensorProduct R S (QuadraticAlgebra R a b) ≃ₐ[S] QuadraticAlgebra S ((algebraMap R S) a) ((algebraMap R S) b)
```

Scalar extension commutes with the coordinate model of a quadratic
algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L41) (line 41).

### QuadraticAlgebra.baseChangeEquiv_tmul

```lean
theorem QuadraticAlgebra.baseChangeEquiv_tmul {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) (s : S) (x : QuadraticAlgebra R a b) : (baseChangeEquiv S a b) (s ⊗ₜ[R] x) = s • { re := (algebraMap R S) x.re, im := (algebraMap R S) x.im }
```

On a pure tensor, base change maps both coordinates into `S` and then
multiplies by the left scalar. No domain assumption is needed.

[Source](../QuadraticAlgebras/FractionRing.lean#L91) (line 91).

### QuadraticAlgebra.baseChangeEquiv_omega

```lean
theorem QuadraticAlgebra.baseChangeEquiv_omega {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) : (baseChangeEquiv S a b) (1 ⊗ₜ[R] omega) = omega
```

Base change sends `1 ⊗ omega` to the distinguished quadratic generator.

[Source](../QuadraticAlgebras/FractionRing.lean#L108) (line 108).

### QuadraticAlgebra.baseChangeEquiv_tmul_one

```lean
theorem QuadraticAlgebra.baseChangeEquiv_tmul_one {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) (s : S) : (baseChangeEquiv S a b) (s ⊗ₜ[R] 1) = (algebraMap S (QuadraticAlgebra S ((algebraMap R S) a) ((algebraMap R S) b))) s
```

Base change sends `s ⊗ 1` to the scalar `s` in the target quadratic algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L117) (line 117).

### QuadraticAlgebra.isLocalization_tensor_fractionRing

```lean
theorem QuadraticAlgebra.isLocalization_tensor_fractionRing {R : Type u} [CommRing R] (a b : R) : IsLocalization (nonZeroDivisors (QuadraticAlgebra R a b)) (TensorProduct R (QuadraticAlgebra R a b) (FractionRing R))
```

Extending scalars from `R` to its total fraction ring already inverts every
regular element of a quadratic algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L125) (line 125).

### QuadraticAlgebra.fractionRingEquivTensor

```lean
noncomputable def QuadraticAlgebra.fractionRingEquivTensor {R : Type u} [CommRing R] (a b : R) : FractionRing (QuadraticAlgebra R a b) ≃ₐ[QuadraticAlgebra R a b] TensorProduct R (QuadraticAlgebra R a b) (FractionRing R)
```

The total fraction ring of a quadratic algebra is its scalar localization
at the regular elements of the base ring.

[Source](../QuadraticAlgebras/FractionRing.lean#L143) (line 143).

### QuadraticAlgebra.fractionRingEquivTensor_algebraMap

```lean
theorem QuadraticAlgebra.fractionRingEquivTensor_algebraMap {R : Type u} [CommRing R] (a b : R) (x : QuadraticAlgebra R a b) : (fractionRingEquivTensor a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) x) = (algebraMap (QuadraticAlgebra R a b) (TensorProduct R (QuadraticAlgebra R a b) (FractionRing R))) x
```

The total-fraction-ring equivalence agrees with the canonical algebra map
on elements of the original quadratic algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L154) (line 154).

### QuadraticAlgebra.fractionRingEquivBaseChange

```lean
noncomputable def QuadraticAlgebra.fractionRingEquivBaseChange {R : Type u} [CommRing R] (a b : R) : FractionRing (QuadraticAlgebra R a b) ≃ₐ[R] QuadraticAlgebra (FractionRing R) ((algebraMap R (FractionRing R)) a) ((algebraMap R (FractionRing R)) b)
```

Coordinate form of the total fraction ring of a quadratic algebra after
extending the two defining coefficients to `FractionRing R`.

[Source](../QuadraticAlgebras/FractionRing.lean#L166) (line 166).

### QuadraticAlgebra.fractionRingEquivBaseChange_algebraMap

```lean
theorem QuadraticAlgebra.fractionRingEquivBaseChange_algebraMap {R : Type u} [CommRing R] (a b : R) (x : QuadraticAlgebra R a b) : (fractionRingEquivBaseChange a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) x) = { re := (algebraMap R (FractionRing R)) x.re, im := (algebraMap R (FractionRing R)) x.im }
```

An original quadratic element maps to the pair of its coordinates in
`FractionRing R` under the total-fraction-ring/base-change equivalence.

[Source](../QuadraticAlgebras/FractionRing.lean#L177) (line 177).

### QuadraticAlgebra.fractionRingEquivBaseChange_omega

```lean
theorem QuadraticAlgebra.fractionRingEquivBaseChange_omega {R : Type u} [CommRing R] (a b : R) : (fractionRingEquivBaseChange a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) omega) = omega
```

The base-change presentation of the total fraction ring preserves `omega`.

[Source](../QuadraticAlgebras/FractionRing.lean#L198) (line 198).

### QuadraticAlgebra.fractionRingEquivAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.fractionRingEquivAdjoinRoot {R : Type u} [CommRing R] (a b : R) : FractionRing (QuadraticAlgebra R a b) ≃ₐ[R] AdjoinRoot (definingPolynomial ((algebraMap R (FractionRing R)) a) ((algebraMap R (FractionRing R)) b))
```

Polynomial-quotient form of the total fraction ring of a quadratic
algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L208) (line 208).

### QuadraticAlgebra.fractionRingEquivAdjoinRoot_omega

```lean
theorem QuadraticAlgebra.fractionRingEquivAdjoinRoot_omega {R : Type u} [CommRing R] (a b : R) : (fractionRingEquivAdjoinRoot a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) omega) = AdjoinRoot.root (definingPolynomial ((algebraMap R (FractionRing R)) a) ((algebraMap R (FractionRing R)) b))
```

The quotient presentation of the total fraction ring sends the embedded
`omega` to the root of the quadratic with fraction-ring coefficients.

[Source](../QuadraticAlgebras/FractionRing.lean#L220) (line 220).

## Module `QuadraticAlgebras.Squarefree`

> # Squarefree denominators in fraction fields
>
> This file records the denominator argument used in quadratic integral-closure
> criteria.  If `f` is squarefree in a unique factorization domain and `x² f`
> lies in the base ring, then the reduced denominator of `x` must be a unit.
>
> The result is stated for an arbitrary chosen fraction field.  It is not tied
> to a quadratic-algebra presentation.

[Module source](../QuadraticAlgebras/Squarefree.lean)

### IsFractionRing.isInteger_of_sq_mul_squarefree

```lean
theorem IsFractionRing.isInteger_of_sq_mul_squarefree {A : Type u_1} {K : Type u_2} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K] [Algebra A K] [IsFractionRing A K] {f : A} (hf : Squarefree f) {x : K} (hx : IsLocalization.IsInteger A (x ^ 2 * (algebraMap A K) f)) : IsLocalization.IsInteger A x
```

If the square of a fraction times a squarefree base-ring element belongs
to the image of the base ring, then the fraction itself belongs to that image.
Here `IsLocalization.IsInteger` means base-ring membership, not `IsIntegral`.

[Source](../QuadraticAlgebras/Squarefree.lean#L31) (line 31).

## Module `QuadraticAlgebras.Integral`

> # Integral elements in quadratic algebras
>
> This file descends the trace and norm of an integral element of a quadratic
> algebra over a fraction field.  The defining quadratic algebra need not be a
> domain: conjugation preserves integrality, so the trace and norm are integral
> over the base ring, and integral closedness places them back in that ring.

[Module source](../QuadraticAlgebras/Integral.lean)

### QuadraticAlgebra.starAlgEquiv

```lean
noncomputable def QuadraticAlgebra.starAlgEquiv {K : Type v} (R : Type u) [CommRing R] [CommRing K] [Algebra R K] (a b : K) : QuadraticAlgebra K a b ≃ₐ[R] QuadraticAlgebra K a b
```

Quadratic conjugation as an algebra automorphism over any ring acting
through the coefficient ring.

[Source](../QuadraticAlgebras/Integral.lean#L31) (line 31).

### QuadraticAlgebra.starAlgEquiv_apply

```lean
theorem QuadraticAlgebra.starAlgEquiv_apply {K : Type v} (R : Type u) [CommRing R] [CommRing K] [Algebra R K] (a b : K) (x : QuadraticAlgebra K a b) : (starAlgEquiv R a b) x = star x
```

The algebra automorphism `starAlgEquiv` acts by quadratic conjugation.

[Source](../QuadraticAlgebras/Integral.lean#L42) (line 42).

### QuadraticAlgebra.isIntegral_star

```lean
theorem QuadraticAlgebra.isIntegral_star {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K] {a b : K} {x : QuadraticAlgebra K a b} (hx : IsIntegral R x) : IsIntegral R (star x)
```

Conjugating a quadratic element preserves integrality over the base ring,
without requiring the quadratic algebra or coefficient ring to be a domain.

[Source](../QuadraticAlgebras/Integral.lean#L49) (line 49).

### QuadraticAlgebra.isInteger_trace_of_isIntegral

```lean
theorem QuadraticAlgebra.isInteger_trace_of_isIntegral {R : Type u} {K : Type v} [CommRing R] [IsIntegrallyClosed R] [CommRing K] [Algebra R K] [IsFractionRing R K] {a b : K} {x : QuadraticAlgebra K a b} (hx : IsIntegral R x) : IsLocalization.IsInteger R (trace x)
```

The trace of an integral quadratic element over an integrally closed base
ring belongs to that base ring.

[Source](../QuadraticAlgebras/Integral.lean#L60) (line 60).

### QuadraticAlgebra.isInteger_norm_of_isIntegral

```lean
theorem QuadraticAlgebra.isInteger_norm_of_isIntegral {R : Type u} {K : Type v} [CommRing R] [IsIntegrallyClosed R] [CommRing K] [Algebra R K] [IsFractionRing R K] {a b : K} {x : QuadraticAlgebra K a b} (hx : IsIntegral R x) : IsLocalization.IsInteger R (norm x)
```

The norm of an integral quadratic element over an integrally closed base
ring belongs to that base ring.

[Source](../QuadraticAlgebras/Integral.lean#L72) (line 72).

## Module `QuadraticAlgebras.IntegralClosure`

> # Integral closure of squarefree quadratic algebras
>
> A domain quadratic algebra `A[ω]` with `ω² = f` is integrally closed when
> `A` is a unique factorization domain, `f` is squarefree, and `2` is
> invertible.  The proof transports an integral element of the total fraction
> ring to the coordinate model over `FractionRing A`.  Its trace and norm
> descend to `A`; the trace recovers the constant coordinate, and squarefree
> denominator descent recovers the linear coordinate.

[Module source](../QuadraticAlgebras/IntegralClosure.lean)

### QuadraticAlgebra.isIntegrallyClosed_of_squarefree

```lean
theorem QuadraticAlgebra.isIntegrallyClosed_of_squarefree {A : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Invertible 2] {f : A} (hf : Squarefree f) [IsDomain (QuadraticAlgebra A f 0)] : IsIntegrallyClosed (QuadraticAlgebra A f 0)
```

A domain quadratic algebra with squarefree radicand over a UFD is
integrally closed when `2` is invertible.

[Source](../QuadraticAlgebras/IntegralClosure.lean#L37) (line 37).

## Module `QuadraticAlgebras.RepeatedSquare`

> # Repeated-square obstructions to quadratic integral closedness
>
> If a nonzero nonunit square divides the radicand `f`, then `omega / p` is an
> integral element of the fraction field of `QuadraticAlgebra A f 0` which does
> not belong to the quadratic algebra.  Consequently a domain quadratic algebra
> over a unique factorization domain cannot be integrally closed when its
> radicand is not squarefree.
>
> The domain hypothesis on the quadratic algebra rules out the zero radicand.
> This boundary is essential: an unconditional nonsquarefree-to-prime-square
> statement is false for zero in a field with no prime elements.

[Module source](../QuadraticAlgebras/RepeatedSquare.lean)

### QuadraticAlgebra.radicand_ne_zero_of_isDomain

```lean
theorem QuadraticAlgebra.radicand_ne_zero_of_isDomain {A : Type u} [CommRing A] [IsDomain A] {f : A} [IsDomain (QuadraticAlgebra A f 0)] : f ≠ 0
```

The radicand of a domain quadratic algebra is nonzero.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L38) (line 38).

### QuadraticAlgebra.exists_prime_sq_dvd_of_not_squarefree

```lean
theorem QuadraticAlgebra.exists_prime_sq_dvd_of_not_squarefree {A : Type u} [CommRing A] {f : A} [UniqueFactorizationMonoid A] (hf0 : f ≠ 0) (hf : ¬Squarefree f) : ∃ (p : A), Prime p ∧ p ^ 2 ∣ f
```

A nonzero nonsquarefree element of a UFD has a prime whose square divides
it.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L51) (line 51).

### QuadraticAlgebra.exists_integral_not_mem_range_of_sq_dvd

```lean
theorem QuadraticAlgebra.exists_integral_not_mem_range_of_sq_dvd {A : Type u} [CommRing A] [IsDomain A] {f p : A} [IsDomain (QuadraticAlgebra A f 0)] (hp0 : p ≠ 0) (hp : ¬IsUnit p) (hpf : p ^ 2 ∣ f) : ∃ (x : FractionRing (QuadraticAlgebra A f 0)), IsIntegral (QuadraticAlgebra A f 0) x ∧ x ∉ Set.range ⇑(algebraMap (QuadraticAlgebra A f 0) (FractionRing (QuadraticAlgebra A f 0)))
```

If a nonzero nonunit square divides the radicand, the fraction `omega / p`
is integral over the quadratic algebra but is not in its image.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L62) (line 62).

### QuadraticAlgebra.not_isIntegrallyClosed_of_sq_dvd

```lean
theorem QuadraticAlgebra.not_isIntegrallyClosed_of_sq_dvd {A : Type u} [CommRing A] [IsDomain A] {f p : A} [IsDomain (QuadraticAlgebra A f 0)] (hp0 : p ≠ 0) (hp : ¬IsUnit p) (hpf : p ^ 2 ∣ f) : ¬IsIntegrallyClosed (QuadraticAlgebra A f 0)
```

A domain quadratic algebra is not integrally closed when its radicand has
a nonzero nonunit square divisor.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L139) (line 139).

### QuadraticAlgebra.not_isIntegrallyClosed_of_not_squarefree

```lean
theorem QuadraticAlgebra.not_isIntegrallyClosed_of_not_squarefree {A : Type u} [CommRing A] [IsDomain A] {f : A} [UniqueFactorizationMonoid A] [IsDomain (QuadraticAlgebra A f 0)] (hf : ¬Squarefree f) : ¬IsIntegrallyClosed (QuadraticAlgebra A f 0)
```

A domain quadratic algebra over a UFD is not integrally closed when its
radicand is not squarefree.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L151) (line 151).

## Module `QuadraticAlgebras.IntegralClosureCriterion`

> # Integral closedness criterion for quadratic algebras
>
> A domain quadratic algebra `A[ω]` with `ω² = f` over a unique factorization
> domain, with `2` invertible, is integrally closed exactly when `f` is
> squarefree.  This combines the squarefree integral-closedness theorem with the
> repeated-square obstruction.

[Module source](../QuadraticAlgebras/IntegralClosureCriterion.lean)

### QuadraticAlgebra.isIntegrallyClosed_iff_squarefree

```lean
theorem QuadraticAlgebra.isIntegrallyClosed_iff_squarefree {A : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Invertible 2] {f : A} [IsDomain (QuadraticAlgebra A f 0)] : IsIntegrallyClosed (QuadraticAlgebra A f 0) ↔ Squarefree f
```

A domain quadratic algebra over a UFD, with `2` invertible, is integrally
closed if and only if its radicand is squarefree.

[Source](../QuadraticAlgebras/IntegralClosureCriterion.lean#L33) (line 33).

## Module `QuadraticAlgebras.IntegralClosureInt`

> # Integral closure of quadratic algebras over the integers
>
> The quadratic algebra `ℤ[ω]` with `ω² = f` is a domain and is integrally
> closed when `f` is squarefree and congruent to `2` or `3` modulo `4`. The proof
> descends twice each coordinate from the total fraction ring using the trace,
> norm, and squarefree denominator descent. The congruence condition then forces
> both descended integer coordinates to be even.

[Module source](../QuadraticAlgebras/IntegralClosureInt.lean)

### QuadraticAlgebra.isDomain_int_of_emod_four

```lean
theorem QuadraticAlgebra.isDomain_int_of_emod_four {f : ℤ} (hmod : f % 4 = 2 ∨ f % 4 = 3) : IsDomain (QuadraticAlgebra ℤ f 0)
```

If an integer is congruent to `2` or `3` modulo `4`, then adjoining a
square root of it to the integers gives a domain.

[Source](../QuadraticAlgebras/IntegralClosureInt.lean#L30) (line 30).

### QuadraticAlgebra.isIntegrallyClosed_int_of_squarefree_of_emod_four

```lean
theorem QuadraticAlgebra.isIntegrallyClosed_int_of_squarefree_of_emod_four {f : ℤ} (hf : Squarefree f) (hmod : f % 4 = 2 ∨ f % 4 = 3) : IsIntegrallyClosed (QuadraticAlgebra ℤ f 0)
```

A quadratic algebra over the integers with squarefree radicand is
integrally closed when the radicand is congruent to `2` or `3` modulo `4`.

[Source](../QuadraticAlgebras/IntegralClosureInt.lean#L129) (line 129).

## Module `QuadraticAlgebras.Dedekind`

> # Dedekind quadratic algebras
>
> This file packages the generic passage from integral closedness to the
> Dedekind-domain property for a quadratic algebra over a Dedekind domain. The
> quadratic algebra is finite as a module over its base, so it is Noetherian;
> integrality bounds its Krull dimension by one.

[Module source](../QuadraticAlgebras/Dedekind.lean)

### QuadraticAlgebra.isDedekindDomain_of_isIntegrallyClosed

```lean
theorem QuadraticAlgebra.isDedekindDomain_of_isIntegrallyClosed {R : Type u} [CommRing R] [IsDedekindDomain R] {a b : R} [IsDomain (QuadraticAlgebra R a b)] [IsIntegrallyClosed (QuadraticAlgebra R a b)] : IsDedekindDomain (QuadraticAlgebra R a b)
```

A domain quadratic algebra over a Dedekind domain is Dedekind when it is
integrally closed.

[Source](../QuadraticAlgebras/Dedekind.lean#L30) (line 30).

## Module `QuadraticAlgebras.Diagonal`

> # Diagonal multivariate quadratics
>
> This file defines the diagonal quadratic `∑ i, c i • X i ^ 2` attached to a
> finitely supported coefficient family.  It proves reusable coefficient,
> homogeneity, irreducibility, and squarefreeness results over fields of
> characteristic different from two.

[Module source](../QuadraticAlgebras/Diagonal.lean)

### MvPolynomial.sumSMulXSq

```lean
noncomputable def MvPolynomial.sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] : (ι →₀ R) →ₗ[R] MvPolynomial ι R
```

The diagonal quadratic polynomial `∑ i, c i • X i ^ 2`.

[Source](../QuadraticAlgebras/Diagonal.lean#L36) (line 36).

### MvPolynomial.sumSMulXSq_apply

```lean
theorem MvPolynomial.sumSMulXSq_apply {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) : sumSMulXSq c = c.sum fun (i : ι) (a : R) => a • X i ^ 2
```

Evaluate the linear construction as the finite sum of its diagonal terms.

[Source](../QuadraticAlgebras/Diagonal.lean#L42) (line 42).

### MvPolynomial.coeff_sumSMulXSq

```lean
theorem MvPolynomial.coeff_sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) (i : ι) : (sumSMulXSq c).coeff (Finsupp.single i 2) = c i
```

The coefficient of the monomial `X i ^ 2` is the given coefficient `c i`.

[Source](../QuadraticAlgebras/Diagonal.lean#L47) (line 47).

### MvPolynomial.pderiv_sumSMulXSq

```lean
theorem MvPolynomial.pderiv_sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) (i : ι) : (pderiv i) (sumSMulXSq c) = C (2 * c i) * X i
```

The derivative in variable `i` is `2 * c i * X i`, over any commutative
ring, including characteristic two.

[Source](../QuadraticAlgebras/Diagonal.lean#L60) (line 60).

### MvPolynomial.isHomogeneous_sumSMulXSq

```lean
theorem MvPolynomial.isHomogeneous_sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) : (sumSMulXSq c).IsHomogeneous 2
```

A diagonal quadratic is homogeneous of degree two, also when all its
coefficients vanish; no field or nonzero-coefficient hypothesis is required.

[Source](../QuadraticAlgebras/Diagonal.lean#L79) (line 79).

### MvPolynomial.irreducible_sumSMulXSq

```lean
theorem MvPolynomial.irreducible_sumSMulXSq {ι : Type u_1} {k : Type u_3} [Field k] [NeZero 2] (c : ι →₀ k) (hc : 3 ≤ c.support.card) : Irreducible (sumSMulXSq c)
```

A diagonal quadratic over a field of characteristic different from two is
irreducible as soon as at least three coefficients are nonzero.

[Source](../QuadraticAlgebras/Diagonal.lean#L213) (line 213).

### MvPolynomial.irreducible_C_mul_X_sq_add_C_mul_X_sq_of_not_isSquare

```lean
theorem MvPolynomial.irreducible_C_mul_X_sq_add_C_mul_X_sq_of_not_isSquare {ι : Type u_1} {k : Type u_3} [Field k] [NeZero 2] {i j : ι} (hij : i ≠ j) {a b : k} (ha0 : a ≠ 0) (hnsq : ¬IsSquare (-b / a)) : Irreducible (C a * X i ^ 2 + C b * X j ^ 2)
```

A binary diagonal quadratic `a * X i ^ 2 + b * X j ^ 2` over a field of
characteristic different from two is irreducible when `i ≠ j`, `a` is
nonzero, and `-b / a` is not a square. (The last condition already forces
`b` to be nonzero.)

[Source](../QuadraticAlgebras/Diagonal.lean#L345) (line 345).

### MvPolynomial.squarefree_sumSMulXSq

```lean
theorem MvPolynomial.squarefree_sumSMulXSq {ι : Type u_1} {k : Type u_3} [Field k] [NeZero 2] (c : ι →₀ k) (hc : c.support.Nontrivial) : Squarefree (sumSMulXSq c)
```

A diagonal quadratic over a field of characteristic different from two is
squarefree as soon as at least two coefficients are nonzero.

[Source](../QuadraticAlgebras/Diagonal.lean#L427) (line 427).

## Module `QuadraticAlgebras.SqrtNegFive`

> # The arithmetic quadratic algebra of `√-5` is not a UFD
>
> This file proves that `QuadraticAlgebra ℤ (-5) 0` is not a unique
> factorization monoid. The embedded integer `2` is irreducible because the norm
> form `x² + 5y²` does not represent `2`, but it is not prime because
> `(1 + ω) * (1 - ω) = 6` while `2` divides neither factor.

[Module source](../QuadraticAlgebras/SqrtNegFive.lean)

### QuadraticAlgebra.norm_int_negFive_eq

```lean
theorem QuadraticAlgebra.norm_int_negFive_eq (x : QuadraticAlgebra ℤ (-5) 0) : norm x = x.re ^ 2 + 5 * x.im ^ 2
```

In the integer quadratic algebra with `ω² = -5`, the norm is
`x.re² + 5 * x.im²`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L26) (line 26).

### QuadraticAlgebra.isUnit_iff_norm_eq_one_int_negFive

```lean
theorem QuadraticAlgebra.isUnit_iff_norm_eq_one_int_negFive {x : QuadraticAlgebra ℤ (-5) 0} : IsUnit x ↔ norm x = 1
```

An element of `QuadraticAlgebra ℤ (-5) 0` is a unit exactly when its norm
is `1`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L38) (line 38).

### QuadraticAlgebra.irreducible_two_int_negFive

```lean
theorem QuadraticAlgebra.irreducible_two_int_negFive : Irreducible 2
```

The embedded integer `2` is irreducible in
`QuadraticAlgebra ℤ (-5) 0`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L66) (line 66).

### QuadraticAlgebra.not_prime_two_int_negFive

```lean
theorem QuadraticAlgebra.not_prime_two_int_negFive : ¬Prime 2
```

The embedded integer `2` is not prime in
`QuadraticAlgebra ℤ (-5) 0`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L122) (line 122).

### QuadraticAlgebra.not_uniqueFactorizationMonoid_int_negFive

```lean
theorem QuadraticAlgebra.not_uniqueFactorizationMonoid_int_negFive : ¬UniqueFactorizationMonoid (QuadraticAlgebra ℤ (-5) 0)
```

The integer quadratic algebra `QuadraticAlgebra ℤ (-5) 0` is not a unique
factorization monoid.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L136) (line 136).

## Module `QuadraticAlgebras.NumberField`

> # Number fields from integer quadratic algebras
>
> This file connects the coordinate model `QuadraticAlgebra ℤ a b` to the
> number-field API.  It also records the elementary degree, discriminant,
> signature, and Minkowski-bound computations for `ℤ[√-5]`.
>
> The separate `QuadraticAlgebras.ClassNumberNegFive` module builds on these
> results to classify the ideals of norm at most two and compute the class number.

[Module source](../QuadraticAlgebras/NumberField.lean)

### QuadraticAlgebra.mapCoeffsEquiv

```lean
def QuadraticAlgebra.mapCoeffsEquiv {S : Type u_1} {T : Type u_2} [CommRing S] [CommRing T] (e : S ≃+* T) (a b : S) : QuadraticAlgebra S a b ≃+* QuadraticAlgebra T (e a) (e b)
```

Transport a quadratic algebra along a ring equivalence of its
coefficients.

[Source](../QuadraticAlgebras/NumberField.lean#L31) (line 31).

### QuadraticAlgebra.mapCoeffsEquivOfEq

```lean
def QuadraticAlgebra.mapCoeffsEquivOfEq {S : Type u_1} {T : Type u_2} [CommRing S] [CommRing T] (e : S ≃+* T) {a b : S} (a' b' : T) (ha : e a = a') (hb : e b = b') : QuadraticAlgebra S a b ≃+* QuadraticAlgebra T a' b'
```

Transport a quadratic algebra along a ring equivalence, with the target
coefficients presented by equalities.

[Source](../QuadraticAlgebras/NumberField.lean#L44) (line 44).

### QuadraticAlgebra.numberField_fractionRing

```lean
instance QuadraticAlgebra.numberField_fractionRing (a b : ℤ) [IsDomain (QuadraticAlgebra ℤ a b)] : NumberField (FractionRing (QuadraticAlgebra ℤ a b))
```

The fraction field of a domain integer quadratic algebra is a number
field.

[Source](../QuadraticAlgebras/NumberField.lean#L56) (line 56).

### QuadraticAlgebra.ringOfIntegersEquiv

```lean
noncomputable def QuadraticAlgebra.ringOfIntegersEquiv (a b : ℤ) [IsDomain (QuadraticAlgebra ℤ a b)] [IsIntegrallyClosed (QuadraticAlgebra ℤ a b)] : QuadraticAlgebra ℤ a b ≃+* NumberField.RingOfIntegers (FractionRing (QuadraticAlgebra ℤ a b))
```

An integrally closed domain integer quadratic algebra is canonically the
ring of integers of its fraction field.

[Source](../QuadraticAlgebras/NumberField.lean#L74) (line 74).

### QuadraticAlgebra.SqrtNegFiveOrder

```lean
abbrev QuadraticAlgebra.SqrtNegFiveOrder : Type
```

The integer quadratic order `ℤ[√-5]`.

[Source](../QuadraticAlgebras/NumberField.lean#L90) (line 90).

### QuadraticAlgebra.SqrtNegFiveField

```lean
abbrev QuadraticAlgebra.SqrtNegFiveField : Type
```

The fraction field of `ℤ[√-5]`.

[Source](../QuadraticAlgebras/NumberField.lean#L93) (line 93).

### QuadraticAlgebra.instIsDomainSqrtNegFiveOrder

```lean
instance QuadraticAlgebra.instIsDomainSqrtNegFiveOrder : IsDomain SqrtNegFiveOrder
```

The integer order `ℤ[√-5]` is a domain, using `-5 ≡ 3 mod 4`.

[Source](../QuadraticAlgebras/NumberField.lean#L96) (line 96).

### QuadraticAlgebra.instIsIntegrallyClosedSqrtNegFiveOrder

```lean
instance QuadraticAlgebra.instIsIntegrallyClosedSqrtNegFiveOrder : IsIntegrallyClosed SqrtNegFiveOrder
```

Squarefreeness of `-5` and its remainder modulo four make `ℤ[√-5]`
integrally closed. This is a global instance for the specified order.

[Source](../QuadraticAlgebras/NumberField.lean#L100) (line 100).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersEquiv

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersEquiv : SqrtNegFiveOrder ≃+* NumberField.RingOfIntegers SqrtNegFiveField
```

The canonical identification of `ℤ[√-5]` with the ring of integers of its
fraction field.

[Source](../QuadraticAlgebras/NumberField.lean#L107) (line 107).

### QuadraticAlgebra.algebraTrace_eq_trace_sqrtNegFive

```lean
theorem QuadraticAlgebra.algebraTrace_eq_trace_sqrtNegFive (x : SqrtNegFiveOrder) : (Algebra.trace ℤ SqrtNegFiveOrder) x = trace x
```

On `ℤ[√-5]`, algebra trace agrees with quadratic-algebra trace.

[Source](../QuadraticAlgebras/NumberField.lean#L114) (line 114).

### QuadraticAlgebra.discr_sqrtNegFiveOrder_basis

```lean
theorem QuadraticAlgebra.discr_sqrtNegFiveOrder_basis : Algebra.discr ℤ ⇑(basis (-5) 0) = -20
```

The standard basis of `ℤ[√-5]` has discriminant `-20`.

[Source](../QuadraticAlgebras/NumberField.lean#L122) (line 122).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersBasis

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersBasis : Module.Basis (Fin 2) ℤ (NumberField.RingOfIntegers SqrtNegFiveField)
```

The integral basis of the number field induced by the standard basis of
`ℤ[√-5]`.

[Source](../QuadraticAlgebras/NumberField.lean#L129) (line 129).

### QuadraticAlgebra.discr_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.discr_sqrtNegFiveField : NumberField.discr SqrtNegFiveField = -20
```

The number-field discriminant of `ℚ(√-5)` is `-20`.

[Source](../QuadraticAlgebras/NumberField.lean#L138) (line 138).

### QuadraticAlgebra.sqrtNegFiveFieldEquivRatQuadratic

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveFieldEquivRatQuadratic : SqrtNegFiveField ≃ₐ[ℚ] QuadraticAlgebra ℚ (-5) 0
```

The fraction field of `ℤ[√-5]` as the corresponding rational quadratic
algebra.

[Source](../QuadraticAlgebras/NumberField.lean#L150) (line 150).

### QuadraticAlgebra.finrank_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.finrank_sqrtNegFiveField : Module.finrank ℚ SqrtNegFiveField = 2
```

The degree of `ℚ(√-5)` over `ℚ` is two.

[Source](../QuadraticAlgebras/NumberField.lean#L170) (line 170).

### QuadraticAlgebra.instIsTotallyComplexSqrtNegFiveField

```lean
instance QuadraticAlgebra.instIsTotallyComplexSqrtNegFiveField : NumberField.IsTotallyComplex SqrtNegFiveField
```

The field `ℚ(√-5)` is totally complex: a real embedding would send a square
to `-5`, contradicting nonnegativity of real squares.

[Source](../QuadraticAlgebras/NumberField.lean#L176) (line 176).

### QuadraticAlgebra.nrComplexPlaces_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.nrComplexPlaces_sqrtNegFiveField : NumberField.InfinitePlace.nrComplexPlaces SqrtNegFiveField = 1
```

The number field `ℚ(√-5)` has exactly one complex place.

[Source](../QuadraticAlgebras/NumberField.lean#L193) (line 193).

### QuadraticAlgebra.classGroup_minkowskiBound_sqrtNegFiveField_lt_three

```lean
theorem QuadraticAlgebra.classGroup_minkowskiBound_sqrtNegFiveField_lt_three : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces SqrtNegFiveField * (↑(Module.finrank ℚ SqrtNegFiveField).factorial / ↑(Module.finrank ℚ SqrtNegFiveField) ^ Module.finrank ℚ SqrtNegFiveField * √|↑(NumberField.discr SqrtNegFiveField)|) < 3
```

The explicit Minkowski bound for ideal-class representatives in
`ℚ(√-5)` is strictly less than three.

[Source](../QuadraticAlgebras/NumberField.lean#L202) (line 202).

### QuadraticAlgebra.exists_ideal_in_class_of_absNorm_le_two

```lean
theorem QuadraticAlgebra.exists_ideal_in_class_of_absNorm_le_two (C : ClassGroup (NumberField.RingOfIntegers SqrtNegFiveField)) : ∃ (I : ↥(nonZeroDivisors (Ideal (NumberField.RingOfIntegers SqrtNegFiveField)))), ClassGroup.mk0 I = C ∧ Ideal.absNorm ↑I ≤ 2
```

Every ideal class of `ℚ(√-5)` has an integral representative of absolute
norm at most two.

[Source](../QuadraticAlgebras/NumberField.lean#L223) (line 223).

## Module `QuadraticAlgebras.ClassNumberNegFive`

> # The class number of `ℚ(√-5)`
>
> This file classifies the integral ideals of absolute norm at most two in the
> ring of integers of `ℚ(√-5)`.  The unique ideal of norm two is obtained as the
> kernel of reduction to `ZMod 2`; it is nonprincipal.  Combining this
> classification with the Minkowski representative bound proves that the class
> number is two.
>
> The localization and basic-open calculations motivated by this example are
> separate from the source-independent number-field theory developed here.

[Module source](../QuadraticAlgebras/ClassNumberNegFive.lean)

### QuadraticAlgebra.sqrtNegFiveModTwo

```lean
def QuadraticAlgebra.sqrtNegFiveModTwo : SqrtNegFiveOrder →+* ZMod 2
```

Reduction of `ℤ[√-5]` modulo the relation sending `√-5` to `1` in
`ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L32) (line 32).

### QuadraticAlgebra.sqrtNegFiveModTwo_surjective

```lean
theorem QuadraticAlgebra.sqrtNegFiveModTwo_surjective : Function.Surjective ⇑sqrtNegFiveModTwo
```

Reduction from `ℤ[√-5]` to `ZMod 2` is surjective.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L39) (line 39).

### QuadraticAlgebra.sqrtNegFiveIdealTwo

```lean
def QuadraticAlgebra.sqrtNegFiveIdealTwo : Ideal SqrtNegFiveOrder
```

The distinguished ideal of `ℤ[√-5]` obtained as the kernel of reduction
to `ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L44) (line 44).

### QuadraticAlgebra.quotientSqrtNegFiveIdealTwoEquiv

```lean
noncomputable def QuadraticAlgebra.quotientSqrtNegFiveIdealTwoEquiv : SqrtNegFiveOrder ⧸ sqrtNegFiveIdealTwo ≃+* ZMod 2
```

The quotient of `ℤ[√-5]` by its distinguished norm-two ideal is
`ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L50) (line 50).

### QuadraticAlgebra.instIsDedekindDomainSqrtNegFiveOrder

```lean
instance QuadraticAlgebra.instIsDedekindDomainSqrtNegFiveOrder : IsDedekindDomain SqrtNegFiveOrder
```

The integrally closed negative-five quadratic order is a Dedekind
domain.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L57) (line 57).

### QuadraticAlgebra.absNorm_sqrtNegFiveIdealTwo

```lean
theorem QuadraticAlgebra.absNorm_sqrtNegFiveIdealTwo : Ideal.absNorm sqrtNegFiveIdealTwo = 2
```

The distinguished ideal of `ℤ[√-5]` has absolute norm two.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L62) (line 62).

### QuadraticAlgebra.algebraNorm_eq_norm_sqrtNegFive

```lean
theorem QuadraticAlgebra.algebraNorm_eq_norm_sqrtNegFive (x : SqrtNegFiveOrder) : (Algebra.norm ℤ) x = norm x
```

On `ℤ[√-5]`, the algebra norm agrees with the quadratic-algebra norm.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L69) (line 69).

### QuadraticAlgebra.not_isPrincipal_sqrtNegFiveIdealTwo

```lean
theorem QuadraticAlgebra.not_isPrincipal_sqrtNegFiveIdealTwo : ¬Submodule.IsPrincipal sqrtNegFiveIdealTwo
```

The distinguished norm-two ideal of `ℤ[√-5]` is not principal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L76) (line 76).

### QuadraticAlgebra.eq_sqrtNegFiveIdealTwo_of_absNorm_eq_two

```lean
theorem QuadraticAlgebra.eq_sqrtNegFiveIdealTwo_of_absNorm_eq_two (I : Ideal SqrtNegFiveOrder) (hI : Ideal.absNorm I = 2) : I = sqrtNegFiveIdealTwo
```

Every ideal of `ℤ[√-5]` of absolute norm two is the distinguished kernel
ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L102) (line 102).

### QuadraticAlgebra.SqrtNegFiveRingOfIntegers

```lean
abbrev QuadraticAlgebra.SqrtNegFiveRingOfIntegers : Type
```

The ring of integers of `ℚ(√-5)`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L147) (line 147).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo : SqrtNegFiveRingOfIntegers →+* ZMod 2
```

Reduction of the ring of integers of `ℚ(√-5)` to `ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L151) (line 151).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo_surjective

```lean
theorem QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo_surjective : Function.Surjective ⇑sqrtNegFiveRingOfIntegersModTwo
```

Reduction of the ring of integers of `ℚ(√-5)` to `ZMod 2` is
surjective.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L157) (line 157).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwo

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwo : Ideal SqrtNegFiveRingOfIntegers
```

The distinguished norm-two ideal in the ring of integers of `ℚ(√-5)`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L164) (line 164).

### QuadraticAlgebra.quotientSqrtNegFiveRingOfIntegersIdealTwoEquiv

```lean
noncomputable def QuadraticAlgebra.quotientSqrtNegFiveRingOfIntegersIdealTwoEquiv : SqrtNegFiveRingOfIntegers ⧸ sqrtNegFiveRingOfIntegersIdealTwo ≃+* ZMod 2
```

The quotient of the ring of integers of `ℚ(√-5)` by its distinguished
norm-two ideal is `ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L170) (line 170).

### QuadraticAlgebra.absNorm_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.absNorm_sqrtNegFiveRingOfIntegersIdealTwo : Ideal.absNorm sqrtNegFiveRingOfIntegersIdealTwo = 2
```

The distinguished ideal in the ring of integers of `ℚ(√-5)` has absolute
norm two.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L178) (line 178).

### QuadraticAlgebra.comap_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.comap_sqrtNegFiveRingOfIntegersIdealTwo : Ideal.comap sqrtNegFiveRingOfIntegersEquiv.toRingHom sqrtNegFiveRingOfIntegersIdealTwo = sqrtNegFiveIdealTwo
```

Pulling back the distinguished ideal of the ring of integers recovers the
distinguished ideal of `ℤ[√-5]`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L186) (line 186).

### QuadraticAlgebra.not_isPrincipal_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.not_isPrincipal_sqrtNegFiveRingOfIntegersIdealTwo : ¬Submodule.IsPrincipal sqrtNegFiveRingOfIntegersIdealTwo
```

The distinguished norm-two ideal in the ring of integers of `ℚ(√-5)` is
not principal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L196) (line 196).

### QuadraticAlgebra.ringHom_eq_sqrtNegFiveRingOfIntegersModTwo

```lean
theorem QuadraticAlgebra.ringHom_eq_sqrtNegFiveRingOfIntegersModTwo (f : SqrtNegFiveRingOfIntegers →+* ZMod 2) : f = sqrtNegFiveRingOfIntegersModTwo
```

Every ring homomorphism from the ring of integers of `ℚ(√-5)` to
`ZMod 2` is the distinguished reduction map.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L212) (line 212).

### QuadraticAlgebra.eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_eq_two

```lean
theorem QuadraticAlgebra.eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_eq_two (I : Ideal SqrtNegFiveRingOfIntegers) (hI : Ideal.absNorm I = 2) : I = sqrtNegFiveRingOfIntegersIdealTwo
```

Every ideal of absolute norm two in the ring of integers of `ℚ(√-5)` is
the distinguished kernel ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L240) (line 240).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwoNonzero

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwoNonzero : ↥(nonZeroDivisors (Ideal SqrtNegFiveRingOfIntegers))
```

The distinguished norm-two ideal, packaged as a nonzero ideal for the
class-group API.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L271) (line 271).

### QuadraticAlgebra.eq_top_or_eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_le_two

```lean
theorem QuadraticAlgebra.eq_top_or_eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_le_two (I : ↥(nonZeroDivisors (Ideal SqrtNegFiveRingOfIntegers))) (hI : Ideal.absNorm ↑I ≤ 2) : ↑I = ⊤ ∨ ↑I = sqrtNegFiveRingOfIntegersIdealTwo
```

A nonzero ideal of absolute norm at most two in the ring of integers of
`ℚ(√-5)` is either the unit ideal or the distinguished norm-two ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L283) (line 283).

### QuadraticAlgebra.classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo (C : ClassGroup SqrtNegFiveRingOfIntegers) : C = 1 ∨ C = ClassGroup.mk0 sqrtNegFiveRingOfIntegersIdealTwoNonzero
```

Every ideal class of `ℚ(√-5)` is either trivial or represented by the
distinguished norm-two ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L301) (line 301).

### QuadraticAlgebra.classNumber_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.classNumber_sqrtNegFiveField : NumberField.classNumber SqrtNegFiveField = 2
```

The class number of `ℚ(√-5)` is two.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L320) (line 320).

## Module `QuadraticAlgebras`

> # Quadratic algebras
>
> The public aggregate re-exports the coordinate, fraction-ring, integral-closure,
> diagonal-quadratic and negative-five number-field developments.

[Module source](../QuadraticAlgebras.lean)

## Module `QuadraticAlgebrasTest.LeafClient`

> # Direct-leaf downstream checks
>
> All declarations are named and private: these tests use public imports without
> adding anything to the mathematical library's exported interface.

[Module source](../QuadraticAlgebrasTest/LeafClient.lean)

## Module `QuadraticAlgebrasTest.RootClient`

> # Aggregate-only downstream checks
>
> The sole import is the public library root. Named private declarations check its
> exports and ordinary use without re-exporting test material.

[Module source](../QuadraticAlgebrasTest/RootClient.lean)

## Module `QuadraticAlgebrasTest.ReadmeScalarExtension`

> # README scalar-extension example
>
> Scalar extension over arbitrary commutative rings and reduction of the
> defining polynomial.
>
> This named private client is the corresponding README Lean block. It adds no public API.

[Module source](../QuadraticAlgebrasTest/ReadmeScalarExtension.lean)

## Module `QuadraticAlgebrasTest.ReadmeIntegralClosure`

> # README integral-closure example
>
> The generic squarefree criterion and the separate integer congruence criterion.
>
> This named private client is the corresponding README Lean block. It adds no public API.

[Module source](../QuadraticAlgebrasTest/ReadmeIntegralClosure.lean)

## Module `QuadraticAlgebrasTest.ReadmeDiagonal`

> # README diagonal-quadratic example
>
> Diagonal differentiation over rings and squarefreeness in characteristic
> different from two.
>
> This named private client is the corresponding README Lean block. It adds no public API.

[Module source](../QuadraticAlgebrasTest/ReadmeDiagonal.lean)

## Module `QuadraticAlgebrasTest.ReadmeNegativeFive`

> # README negative-five example
>
> The discriminant and class number of the field generated by a square root
> of minus five.
>
> This named private client is the corresponding README Lean block. It adds no public API.

[Module source](../QuadraticAlgebrasTest/ReadmeNegativeFive.lean)
