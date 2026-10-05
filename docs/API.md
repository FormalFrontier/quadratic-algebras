# API reference

Complete public API of quadratic-algebras: 92 declarations in thirteen mathematical leaves.
Import `QuadraticAlgebras` for all leaves. Six test modules contain private checked
clients and README examples, not additional public API.

The 92 Lean signature blocks are inherited unchanged from the
[published native API](https://github.com/FormalFrontier/quadratic-algebras/blob/e5ac018d29892d2a8612f4ca8d4babaabb9c4d15/docs/API.md),
with all displayed implicit arguments retained; they are not proof bodies.
Native printing can suppress type annotations on literals. Consult the linked
source for explicit types; universe parameters are arbitrary. Module explanations,
declaration docstrings and relative source links are maintained against the
current source comments, not newly generated native records. The
[historical input manifest](api-manifest.json) and [binding guide](README.md)
distinguish that native analysis from these edits. See the
[mathematical overview](../README.md).

## Module `QuadraticAlgebras.AdjoinRoot`

> # Quadratic algebras as polynomial quotients
>
> This file identifies mathlib's coordinate model `QuadraticAlgebra R a b`, in
> which `omega ^ 2 = a + b * omega`, with the corresponding `AdjoinRoot` of
> `X ^ 2 - b * X - a`.
>
> ## References
>
> * Mathlib's [quadratic algebra](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/QuadraticAlgebra/Basic.lean)
>   and [adjoined roots](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/AdjoinRoot.lean)
>   provide the two presentations identified here.
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.H, motivates the quadratic integral-closure setting;
>   the equivalence here works over arbitrary commutative rings.

[Module source](../QuadraticAlgebras/AdjoinRoot.lean)

### QuadraticAlgebra.definingPolynomial

```lean
noncomputable def QuadraticAlgebra.definingPolynomial {R : Type u} [CommRing R] (a b : R) : Polynomial R
```

The monic polynomial defining `QuadraticAlgebra R a b`.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L41) (line 41).

### QuadraticAlgebra.definingPolynomial_monic

```lean
theorem QuadraticAlgebra.definingPolynomial_monic {R : Type u} [CommRing R] (a b : R) : (definingPolynomial a b).Monic
```

The defining quadratic is monic over every commutative ring.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L46) (line 46).

### QuadraticAlgebra.fromAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.fromAdjoinRoot {R : Type u} [CommRing R] (a b : R) : AdjoinRoot (definingPolynomial a b) →ₐ[R] QuadraticAlgebra R a b
```

The canonical map from the polynomial-quotient model to the coordinate
model of a quadratic algebra.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L51) (line 51).

### QuadraticAlgebra.fromAdjoinRoot_root

```lean
theorem QuadraticAlgebra.fromAdjoinRoot_root {R : Type u} [CommRing R] (a b : R) : (fromAdjoinRoot a b) (AdjoinRoot.root (definingPolynomial a b)) = omega
```

The quotient-to-coordinate map sends the adjoined root to `omega`.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L61) (line 61).

### QuadraticAlgebra.toAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.toAdjoinRoot {R : Type u} [CommRing R] (a b : R) : QuadraticAlgebra R a b →ₐ[R] AdjoinRoot (definingPolynomial a b)
```

The canonical map from the coordinate model of a quadratic algebra to its
polynomial-quotient model.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L67) (line 67).

### QuadraticAlgebra.toAdjoinRoot_omega

```lean
theorem QuadraticAlgebra.toAdjoinRoot_omega {R : Type u} [CommRing R] (a b : R) : (toAdjoinRoot a b) omega = AdjoinRoot.root (definingPolynomial a b)
```

The coordinate-to-quotient map sends `omega` to the adjoined root.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L88) (line 88).

<a id="qa-equiv-adjoin-root" name="qa-equiv-adjoin-root"></a>

### QuadraticAlgebra.equivAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.equivAdjoinRoot {R : Type u} [CommRing R] (a b : R) : QuadraticAlgebra R a b ≃ₐ[R] AdjoinRoot (definingPolynomial a b)
```

The canonical algebra equivalence between the coordinate and
polynomial-quotient models of a quadratic algebra.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L94) (line 94).

### QuadraticAlgebra.equivAdjoinRoot_apply_omega

```lean
theorem QuadraticAlgebra.equivAdjoinRoot_apply_omega {R : Type u} [CommRing R] (a b : R) : (equivAdjoinRoot a b) omega = AdjoinRoot.root (definingPolynomial a b)
```

The canonical equivalence identifies `omega` with the quotient's root.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L107) (line 107).

### QuadraticAlgebra.equivAdjoinRoot_symm_apply_root

```lean
theorem QuadraticAlgebra.equivAdjoinRoot_symm_apply_root {R : Type u} [CommRing R] (a b : R) : (equivAdjoinRoot a b).symm (AdjoinRoot.root (definingPolynomial a b)) = omega
```

The inverse canonical equivalence identifies the quotient's root with `omega`.

[Source](../QuadraticAlgebras/AdjoinRoot.lean#L113) (line 113).

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
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.H, motivates the passage to fractions in the
>   integral-closure argument; the equivalence here also covers zero divisors.
> * Mathlib's [localization base change](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/Localization/BaseChange.lean)
>   supplies the scalar-extension localization API.

[Module source](../QuadraticAlgebras/FractionRing.lean)

### QuadraticAlgebra.baseChangeEquiv

```lean
noncomputable def QuadraticAlgebra.baseChangeEquiv {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) : TensorProduct R S (QuadraticAlgebra R a b) ≃ₐ[S] QuadraticAlgebra S ((algebraMap R S) a) ((algebraMap R S) b)
```

Scalar extension commutes with the coordinate model of a quadratic
algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L49) (line 49).

### QuadraticAlgebra.baseChangeEquiv_tmul

```lean
theorem QuadraticAlgebra.baseChangeEquiv_tmul {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) (s : S) (x : QuadraticAlgebra R a b) : (baseChangeEquiv S a b) (s ⊗ₜ[R] x) = s • { re := (algebraMap R S) x.re, im := (algebraMap R S) x.im }
```

On a pure tensor, base change maps both coordinates into `S` and then
multiplies by the left scalar. No domain assumption is needed.

[Source](../QuadraticAlgebras/FractionRing.lean#L99) (line 99).

### QuadraticAlgebra.baseChangeEquiv_omega

```lean
theorem QuadraticAlgebra.baseChangeEquiv_omega {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) : (baseChangeEquiv S a b) (1 ⊗ₜ[R] omega) = omega
```

Base change sends `1 ⊗ omega` to the distinguished quadratic generator.

[Source](../QuadraticAlgebras/FractionRing.lean#L116) (line 116).

### QuadraticAlgebra.baseChangeEquiv_tmul_one

```lean
theorem QuadraticAlgebra.baseChangeEquiv_tmul_one {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] (a b : R) (s : S) : (baseChangeEquiv S a b) (s ⊗ₜ[R] 1) = (algebraMap S (QuadraticAlgebra S ((algebraMap R S) a) ((algebraMap R S) b))) s
```

Base change sends `s ⊗ 1` to the scalar `s` in the target quadratic algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L125) (line 125).

### QuadraticAlgebra.isLocalization_tensor_fractionRing

```lean
theorem QuadraticAlgebra.isLocalization_tensor_fractionRing {R : Type u} [CommRing R] (a b : R) : IsLocalization (nonZeroDivisors (QuadraticAlgebra R a b)) (TensorProduct R (QuadraticAlgebra R a b) (FractionRing R))
```

Extending scalars from `R` to its total fraction ring already inverts every
regular element of a quadratic algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L133) (line 133).

### QuadraticAlgebra.fractionRingEquivTensor

```lean
noncomputable def QuadraticAlgebra.fractionRingEquivTensor {R : Type u} [CommRing R] (a b : R) : FractionRing (QuadraticAlgebra R a b) ≃ₐ[QuadraticAlgebra R a b] TensorProduct R (QuadraticAlgebra R a b) (FractionRing R)
```

The total fraction ring of a quadratic algebra is its scalar localization
at the regular elements of the base ring.

[Source](../QuadraticAlgebras/FractionRing.lean#L151) (line 151).

### QuadraticAlgebra.fractionRingEquivTensor_algebraMap

```lean
theorem QuadraticAlgebra.fractionRingEquivTensor_algebraMap {R : Type u} [CommRing R] (a b : R) (x : QuadraticAlgebra R a b) : (fractionRingEquivTensor a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) x) = (algebraMap (QuadraticAlgebra R a b) (TensorProduct R (QuadraticAlgebra R a b) (FractionRing R))) x
```

The total-fraction-ring equivalence agrees with the canonical algebra map
on elements of the original quadratic algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L162) (line 162).

### QuadraticAlgebra.fractionRingEquivBaseChange

```lean
noncomputable def QuadraticAlgebra.fractionRingEquivBaseChange {R : Type u} [CommRing R] (a b : R) : FractionRing (QuadraticAlgebra R a b) ≃ₐ[R] QuadraticAlgebra (FractionRing R) ((algebraMap R (FractionRing R)) a) ((algebraMap R (FractionRing R)) b)
```

Coordinate form of the total fraction ring of a quadratic algebra after
extending the two defining coefficients to `FractionRing R`.

[Source](../QuadraticAlgebras/FractionRing.lean#L174) (line 174).

### QuadraticAlgebra.fractionRingEquivBaseChange_algebraMap

```lean
theorem QuadraticAlgebra.fractionRingEquivBaseChange_algebraMap {R : Type u} [CommRing R] (a b : R) (x : QuadraticAlgebra R a b) : (fractionRingEquivBaseChange a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) x) = { re := (algebraMap R (FractionRing R)) x.re, im := (algebraMap R (FractionRing R)) x.im }
```

An original quadratic element maps to the pair of its coordinates in
`FractionRing R` under the total-fraction-ring/base-change equivalence.

[Source](../QuadraticAlgebras/FractionRing.lean#L185) (line 185).

### QuadraticAlgebra.fractionRingEquivBaseChange_omega

```lean
theorem QuadraticAlgebra.fractionRingEquivBaseChange_omega {R : Type u} [CommRing R] (a b : R) : (fractionRingEquivBaseChange a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) omega) = omega
```

The base-change presentation of the total fraction ring preserves `omega`.

[Source](../QuadraticAlgebras/FractionRing.lean#L206) (line 206).

### QuadraticAlgebra.fractionRingEquivAdjoinRoot

```lean
noncomputable def QuadraticAlgebra.fractionRingEquivAdjoinRoot {R : Type u} [CommRing R] (a b : R) : FractionRing (QuadraticAlgebra R a b) ≃ₐ[R] AdjoinRoot (definingPolynomial ((algebraMap R (FractionRing R)) a) ((algebraMap R (FractionRing R)) b))
```

Polynomial-quotient form of the total fraction ring of a quadratic
algebra.

[Source](../QuadraticAlgebras/FractionRing.lean#L216) (line 216).

### QuadraticAlgebra.fractionRingEquivAdjoinRoot_omega

```lean
theorem QuadraticAlgebra.fractionRingEquivAdjoinRoot_omega {R : Type u} [CommRing R] (a b : R) : (fractionRingEquivAdjoinRoot a b) ((algebraMap (QuadraticAlgebra R a b) (FractionRing (QuadraticAlgebra R a b))) omega) = AdjoinRoot.root (definingPolynomial ((algebraMap R (FractionRing R)) a) ((algebraMap R (FractionRing R)) b))
```

The quotient presentation of the total fraction ring sends the embedded
`omega` to the root of the quadratic with fraction-ring coefficients.

[Source](../QuadraticAlgebras/FractionRing.lean#L228) (line 228).

## Module `QuadraticAlgebras.Squarefree`

> # Squarefree denominators in fraction fields
>
> This file records the denominator argument used in quadratic integral-closure
> criteria.  If `f` is squarefree in a unique factorization domain and `x² f`
> lies in the base ring, then the reduced denominator of `x` must be a unit.
>
> The result is stated for an arbitrary chosen fraction field.  It is not tied
> to a quadratic-algebra presentation.
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.H, supplies the reduced-denominator proof route;
>   this lemma applies to an arbitrary chosen fraction field.
> * Mathlib's [numerator and denominator API](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/Localization/NumDen.lean)
>   provides reduced fractions over a UFD.

[Module source](../QuadraticAlgebras/Squarefree.lean)

### IsFractionRing.isInteger_of_sq_mul_squarefree

```lean
theorem IsFractionRing.isInteger_of_sq_mul_squarefree {A : Type u_1} {K : Type u_2} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K] [Algebra A K] [IsFractionRing A K] {f : A} (hf : Squarefree f) {x : K} (hx : IsLocalization.IsInteger A (x ^ 2 * (algebraMap A K) f)) : IsLocalization.IsInteger A x
```

If the square of a fraction times a squarefree base-ring element belongs
to the image of the base ring, then the fraction itself belongs to that image.
Here `IsLocalization.IsInteger` means base-ring membership, not `IsIntegral`.
The reduced-denominator argument follows Vakil, *The Rising Sea*, Exercise
5.4.H, in this more general fraction-field setting.

[Source](../QuadraticAlgebras/Squarefree.lean#L39) (line 39).

## Module `QuadraticAlgebras.Integral`

> # Integral elements in quadratic algebras
>
> This file descends the trace and norm of an integral element of a quadratic
> algebra over a fraction field.  The defining quadratic algebra need not be a
> domain: conjugation preserves integrality, so the trace and norm are integral
> over the base ring, and integral closedness places them back in that ring.
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.H, supplies the trace-and-norm descent proof route;
>   the statements here do not require a domain quadratic algebra.
> * Mathlib's [integral-closure API](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean)
>   identifies integral elements of a fraction field with base-ring elements.

[Module source](../QuadraticAlgebras/Integral.lean)

### QuadraticAlgebra.starAlgEquiv

```lean
noncomputable def QuadraticAlgebra.starAlgEquiv {K : Type v} (R : Type u) [CommRing R] [CommRing K] [Algebra R K] (a b : K) : QuadraticAlgebra K a b ≃ₐ[R] QuadraticAlgebra K a b
```

Quadratic conjugation as an algebra automorphism over any ring acting
through the coefficient ring.

[Source](../QuadraticAlgebras/Integral.lean#L39) (line 39).

### QuadraticAlgebra.starAlgEquiv_apply

```lean
theorem QuadraticAlgebra.starAlgEquiv_apply {K : Type v} (R : Type u) [CommRing R] [CommRing K] [Algebra R K] (a b : K) (x : QuadraticAlgebra K a b) : (starAlgEquiv R a b) x = star x
```

The algebra automorphism `starAlgEquiv` acts by quadratic conjugation.

[Source](../QuadraticAlgebras/Integral.lean#L50) (line 50).

### QuadraticAlgebra.isIntegral_star

```lean
theorem QuadraticAlgebra.isIntegral_star {R : Type u} {K : Type v} [CommRing R] [CommRing K] [Algebra R K] {a b : K} {x : QuadraticAlgebra K a b} (hx : IsIntegral R x) : IsIntegral R (star x)
```

Conjugating a quadratic element preserves integrality over the base ring,
without requiring the quadratic algebra or coefficient ring to be a domain.

[Source](../QuadraticAlgebras/Integral.lean#L57) (line 57).

### QuadraticAlgebra.isInteger_trace_of_isIntegral

```lean
theorem QuadraticAlgebra.isInteger_trace_of_isIntegral {R : Type u} {K : Type v} [CommRing R] [IsIntegrallyClosed R] [CommRing K] [Algebra R K] [IsFractionRing R K] {a b : K} {x : QuadraticAlgebra K a b} (hx : IsIntegral R x) : IsLocalization.IsInteger R (trace x)
```

The trace of an integral quadratic element over an integrally closed base
ring belongs to that base ring. This trace-descent step follows Vakil,
*The Rising Sea*, Exercise 5.4.H, without requiring a domain quadratic algebra.

[Source](../QuadraticAlgebras/Integral.lean#L68) (line 68).

### QuadraticAlgebra.isInteger_norm_of_isIntegral

```lean
theorem QuadraticAlgebra.isInteger_norm_of_isIntegral {R : Type u} {K : Type v} [CommRing R] [IsIntegrallyClosed R] [CommRing K] [Algebra R K] [IsFractionRing R K] {a b : K} {x : QuadraticAlgebra K a b} (hx : IsIntegral R x) : IsLocalization.IsInteger R (norm x)
```

The norm of an integral quadratic element over an integrally closed base
ring belongs to that base ring. This norm-descent step follows Vakil,
*The Rising Sea*, Exercise 5.4.H, without requiring a domain quadratic algebra.

[Source](../QuadraticAlgebras/Integral.lean#L81) (line 81).

## Module `QuadraticAlgebras.IntegralClosure`

> # Integral closure of squarefree quadratic algebras
>
> A domain quadratic algebra `A[ω]` with `ω² = f` is integrally closed when
> `A` is a unique factorization domain, `f` is squarefree, and `2` is
> invertible.  The proof transports an integral element of the total fraction
> ring to the coordinate model over `FractionRing A`.  Its trace and norm
> descend to `A`; the trace recovers the constant coordinate, and squarefree
> denominator descent recovers the linear coordinate.
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.H, supplies the trace, norm and squarefree
>   denominator proof route used for this direction of the criterion.

[Module source](../QuadraticAlgebras/IntegralClosure.lean)

### QuadraticAlgebra.isIntegrallyClosed_of_squarefree

```lean
theorem QuadraticAlgebra.isIntegrallyClosed_of_squarefree {A : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Invertible 2] {f : A} (hf : Squarefree f) [IsDomain (QuadraticAlgebra A f 0)] : IsIntegrallyClosed (QuadraticAlgebra A f 0)
```

A domain quadratic algebra with squarefree radicand over a UFD is
integrally closed when `2` is invertible. The trace/norm and reduced-denominator
argument follows Vakil, *The Rising Sea*, Exercise 5.4.H.

[Source](../QuadraticAlgebras/IntegralClosure.lean#L43) (line 43).

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
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.H, supplies the repeated-square obstruction;
>   the domain hypothesis and nonzero case are explicit here.
> * Mathlib's [integral-closure API](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean)
>   provides the fraction-ring characterization of integral closedness.

[Module source](../QuadraticAlgebras/RepeatedSquare.lean)

### QuadraticAlgebra.radicand_ne_zero_of_isDomain

```lean
theorem QuadraticAlgebra.radicand_ne_zero_of_isDomain {A : Type u} [CommRing A] [IsDomain A] {f : A} [IsDomain (QuadraticAlgebra A f 0)] : f ≠ 0
```

The radicand of a domain quadratic algebra is nonzero.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L46) (line 46).

### QuadraticAlgebra.exists_prime_sq_dvd_of_not_squarefree

```lean
theorem QuadraticAlgebra.exists_prime_sq_dvd_of_not_squarefree {A : Type u} [CommRing A] {f : A} [UniqueFactorizationMonoid A] (hf0 : f ≠ 0) (hf : ¬Squarefree f) : ∃ (p : A), Prime p ∧ p ^ 2 ∣ f
```

A nonzero nonsquarefree element of a UFD has a prime whose square divides
it.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L59) (line 59).

### QuadraticAlgebra.exists_integral_not_mem_range_of_sq_dvd

```lean
theorem QuadraticAlgebra.exists_integral_not_mem_range_of_sq_dvd {A : Type u} [CommRing A] [IsDomain A] {f p : A} [IsDomain (QuadraticAlgebra A f 0)] (hp0 : p ≠ 0) (hp : ¬IsUnit p) (hpf : p ^ 2 ∣ f) : ∃ (x : FractionRing (QuadraticAlgebra A f 0)), IsIntegral (QuadraticAlgebra A f 0) x ∧ x ∉ Set.range ⇑(algebraMap (QuadraticAlgebra A f 0) (FractionRing (QuadraticAlgebra A f 0)))
```

If a nonzero nonunit square divides the radicand, the fraction `omega / p`
is integral over the quadratic algebra but is not in its image.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L70) (line 70).

### QuadraticAlgebra.not_isIntegrallyClosed_of_sq_dvd

```lean
theorem QuadraticAlgebra.not_isIntegrallyClosed_of_sq_dvd {A : Type u} [CommRing A] [IsDomain A] {f p : A} [IsDomain (QuadraticAlgebra A f 0)] (hp0 : p ≠ 0) (hp : ¬IsUnit p) (hpf : p ^ 2 ∣ f) : ¬IsIntegrallyClosed (QuadraticAlgebra A f 0)
```

A domain quadratic algebra is not integrally closed when its radicand has
a nonzero nonunit square divisor.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L147) (line 147).

### QuadraticAlgebra.not_isIntegrallyClosed_of_not_squarefree

```lean
theorem QuadraticAlgebra.not_isIntegrallyClosed_of_not_squarefree {A : Type u} [CommRing A] [IsDomain A] {f : A} [UniqueFactorizationMonoid A] [IsDomain (QuadraticAlgebra A f 0)] (hf : ¬Squarefree f) : ¬IsIntegrallyClosed (QuadraticAlgebra A f 0)
```

A domain quadratic algebra over a UFD is not integrally closed when its
radicand is not squarefree. The integral `omega / p` obstruction follows Vakil,
*The Rising Sea*, Exercise 5.4.H; the domain assumption excludes the zero case.

[Source](../QuadraticAlgebras/RepeatedSquare.lean#L159) (line 159).

## Module `QuadraticAlgebras.IntegralClosureCriterion`

> # Integral closedness criterion for quadratic algebras
>
> A domain quadratic algebra `A[ω]` with `ω² = f` over a unique factorization
> domain, with `2` invertible, is integrally closed exactly when `f` is
> squarefree.  This combines the squarefree integral-closedness theorem with the
> repeated-square obstruction.
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.H, supplies the trace/norm, reduced-denominator
>   and repeated-square proof route. The criterion here makes its UFD, domain
>   and invertibility hypotheses explicit.

[Module source](../QuadraticAlgebras/IntegralClosureCriterion.lean)

<a id="qa-ufd-squarefree-criterion" name="qa-ufd-squarefree-criterion"></a>

### QuadraticAlgebra.isIntegrallyClosed_iff_squarefree

```lean
theorem QuadraticAlgebra.isIntegrallyClosed_iff_squarefree {A : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Invertible 2] {f : A} [IsDomain (QuadraticAlgebra A f 0)] : IsIntegrallyClosed (QuadraticAlgebra A f 0) ↔ Squarefree f
```

A domain quadratic algebra over a UFD, with `2` invertible, is integrally
closed if and only if its radicand is squarefree. Both directions follow the
proof route in Vakil, *The Rising Sea*, Exercise 5.4.H.

[Source](../QuadraticAlgebras/IntegralClosureCriterion.lean#L40) (line 40).

## Module `QuadraticAlgebras.IntegralClosureInt`

> # Integral closure of quadratic algebras over the integers
>
> The quadratic algebra `ℤ[ω]` with `ω² = f` is a domain and is integrally
> closed when `f` is squarefree and congruent to `2` or `3` modulo `4`. The proof
> descends twice each coordinate from the total fraction ring using the trace,
> norm, and squarefree denominator descent. The congruence condition then forces
> both descended integer coordinates to be even.
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.I(a), motivates this integer congruence case;
>   Exercise 5.4.H supplies the trace/norm and denominator proof route.

[Module source](../QuadraticAlgebras/IntegralClosureInt.lean)

### QuadraticAlgebra.isDomain_int_of_emod_four

```lean
theorem QuadraticAlgebra.isDomain_int_of_emod_four {f : ℤ} (hmod : f % 4 = 2 ∨ f % 4 = 3) : IsDomain (QuadraticAlgebra ℤ f 0)
```

If an integer is congruent to `2` or `3` modulo `4`, then adjoining a
square root of it to the integers gives a domain.

[Source](../QuadraticAlgebras/IntegralClosureInt.lean#L36) (line 36).

<a id="qa-integer-integral-closure" name="qa-integer-integral-closure"></a>

### QuadraticAlgebra.isIntegrallyClosed_int_of_squarefree_of_emod_four

```lean
theorem QuadraticAlgebra.isIntegrallyClosed_int_of_squarefree_of_emod_four {f : ℤ} (hf : Squarefree f) (hmod : f % 4 = 2 ∨ f % 4 = 3) : IsIntegrallyClosed (QuadraticAlgebra ℤ f 0)
```

A quadratic algebra over the integers with squarefree radicand is
integrally closed when the radicand is congruent to `2` or `3` modulo `4`.
Vakil, *The Rising Sea*, Exercise 5.4.I(a), motivates this case; the proof
uses the trace/norm and denominator route of Exercise 5.4.H.

[Source](../QuadraticAlgebras/IntegralClosureInt.lean#L135) (line 135).

## Module `QuadraticAlgebras.Dedekind`

> # Dedekind quadratic algebras
>
> This file packages the generic passage from integral closedness to the
> Dedekind-domain property for a quadratic algebra over a Dedekind domain. The
> quadratic algebra is finite as a module over its base, so it is Noetherian;
> integrality bounds its Krull dimension by one.
>
> ## References
>
> * Mathlib's [Dedekind-domain API](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/DedekindDomain/Basic.lean)
>   supplies the finite-integral dimension and Noetherian-domain results used here.

[Module source](../QuadraticAlgebras/Dedekind.lean)

### QuadraticAlgebra.isDedekindDomain_of_isIntegrallyClosed

```lean
theorem QuadraticAlgebra.isDedekindDomain_of_isIntegrallyClosed {R : Type u} [CommRing R] [IsDedekindDomain R] {a b : R} [IsDomain (QuadraticAlgebra R a b)] [IsIntegrallyClosed (QuadraticAlgebra R a b)] : IsDedekindDomain (QuadraticAlgebra R a b)
```

A domain quadratic algebra over a Dedekind domain is Dedekind when it is
integrally closed.

[Source](../QuadraticAlgebras/Dedekind.lean#L35) (line 35).

## Module `QuadraticAlgebras.Diagonal`

> # Diagonal multivariate quadratics
>
> This file defines the diagonal quadratic `∑ i, c i • X i ^ 2` attached to a
> finitely supported coefficient family.  It proves reusable coefficient,
> homogeneity, irreducibility, and squarefreeness results over fields of
> characteristic different from two.
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.I(b), motivates a diagonal prerequisite, while
>   Exercise 5.4.N motivates the binary diagonal case. These polynomial results
>   alone do not establish the hypersurface-normality exercise.
> * Mathlib's [multivariate quadratic results](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/RingTheory/MvPolynomial/IrreducibleQuadratic.lean)
>   provide the polynomial infrastructure used here.

[Module source](../QuadraticAlgebras/Diagonal.lean)

<a id="qa-diagonal-sum" name="qa-diagonal-sum"></a>

### MvPolynomial.sumSMulXSq

```lean
noncomputable def MvPolynomial.sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] : (ι →₀ R) →ₗ[R] MvPolynomial ι R
```

The diagonal quadratic polynomial `∑ i, c i • X i ^ 2`.

[Source](../QuadraticAlgebras/Diagonal.lean#L45) (line 45).

### MvPolynomial.sumSMulXSq_apply

```lean
theorem MvPolynomial.sumSMulXSq_apply {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) : sumSMulXSq c = c.sum fun (i : ι) (a : R) => a • X i ^ 2
```

Evaluate the linear construction as the finite sum of its diagonal terms.

[Source](../QuadraticAlgebras/Diagonal.lean#L51) (line 51).

### MvPolynomial.coeff_sumSMulXSq

```lean
theorem MvPolynomial.coeff_sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) (i : ι) : (sumSMulXSq c).coeff (Finsupp.single i 2) = c i
```

The coefficient of the monomial `X i ^ 2` is the given coefficient `c i`.

[Source](../QuadraticAlgebras/Diagonal.lean#L56) (line 56).

### MvPolynomial.pderiv_sumSMulXSq

```lean
theorem MvPolynomial.pderiv_sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) (i : ι) : (pderiv i) (sumSMulXSq c) = C (2 * c i) * X i
```

The derivative in variable `i` is `2 * c i * X i`, over any commutative
ring, including characteristic two.

[Source](../QuadraticAlgebras/Diagonal.lean#L69) (line 69).

### MvPolynomial.isHomogeneous_sumSMulXSq

```lean
theorem MvPolynomial.isHomogeneous_sumSMulXSq {ι : Type u_1} {R : Type u_2} [CommRing R] (c : ι →₀ R) : (sumSMulXSq c).IsHomogeneous 2
```

A diagonal quadratic is homogeneous of degree two, also when all its
coefficients vanish; no field or nonzero-coefficient hypothesis is required.

[Source](../QuadraticAlgebras/Diagonal.lean#L88) (line 88).

<a id="qa-diagonal-irreducible" name="qa-diagonal-irreducible"></a>

### MvPolynomial.irreducible_sumSMulXSq

```lean
theorem MvPolynomial.irreducible_sumSMulXSq {ι : Type u_1} {k : Type u_3} [Field k] [NeZero 2] (c : ι →₀ k) (hc : 3 ≤ c.support.card) : Irreducible (sumSMulXSq c)
```

A diagonal quadratic over a field of characteristic different from two is
irreducible as soon as at least three coefficients are nonzero. This reusable
prerequisite is motivated by Vakil, *The Rising Sea*, Exercise 5.4.I(b), not
a proof of the hypersurface-normality exercise.

[Source](../QuadraticAlgebras/Diagonal.lean#L222) (line 222).

<a id="qa-binary-diagonal-irreducible" name="qa-binary-diagonal-irreducible"></a>

### MvPolynomial.irreducible_C_mul_X_sq_add_C_mul_X_sq_of_not_isSquare

```lean
theorem MvPolynomial.irreducible_C_mul_X_sq_add_C_mul_X_sq_of_not_isSquare {ι : Type u_1} {k : Type u_3} [Field k] [NeZero 2] {i j : ι} (hij : i ≠ j) {a b : k} (ha0 : a ≠ 0) (hnsq : ¬IsSquare (-b / a)) : Irreducible (C a * X i ^ 2 + C b * X j ^ 2)
```

A binary diagonal quadratic `a * X i ^ 2 + b * X j ^ 2` over a field of
characteristic different from two is irreducible when `i ≠ j`, `a` is
nonzero, and `-b / a` is not a square. (The last condition already forces
`b` to be nonzero.) The binary case is motivated by Vakil, *The Rising Sea*,
Exercise 5.4.N.

[Source](../QuadraticAlgebras/Diagonal.lean#L356) (line 356).

<a id="qa-diagonal-squarefree" name="qa-diagonal-squarefree"></a>

### MvPolynomial.squarefree_sumSMulXSq

```lean
theorem MvPolynomial.squarefree_sumSMulXSq {ι : Type u_1} {k : Type u_3} [Field k] [NeZero 2] (c : ι →₀ k) (hc : c.support.Nontrivial) : Squarefree (sumSMulXSq c)
```

A diagonal quadratic over a field of characteristic different from two is
squarefree as soon as at least two coefficients are nonzero.

[Source](../QuadraticAlgebras/Diagonal.lean#L439) (line 439).

## Module `QuadraticAlgebras.SqrtNegFive`

> # The arithmetic quadratic algebra of `√-5` is not a UFD
>
> This file proves that `QuadraticAlgebra ℤ (-5) 0` is not a unique
> factorization monoid. The embedded integer `2` is irreducible because the norm
> form `x² + 5y²` does not represent `2`, but it is not prime because
> `(1 + ω) * (1 - ω) = 6` while `2` divides neither factor.
>
> ## References
>
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.K, motivates the `√-5` example and gives the
>   factorization hint behind its failure of unique factorization.
> * Mathlib's [quadratic algebra](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/QuadraticAlgebra/Basic.lean)
>   supplies the coordinate norm and conjugation operations.

[Module source](../QuadraticAlgebras/SqrtNegFive.lean)

### QuadraticAlgebra.norm_int_negFive_eq

```lean
theorem QuadraticAlgebra.norm_int_negFive_eq (x : QuadraticAlgebra ℤ (-5) 0) : norm x = x.re ^ 2 + 5 * x.im ^ 2
```

In the integer quadratic algebra with `ω² = -5`, the norm is
`x.re² + 5 * x.im²`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L34) (line 34).

### QuadraticAlgebra.isUnit_iff_norm_eq_one_int_negFive

```lean
theorem QuadraticAlgebra.isUnit_iff_norm_eq_one_int_negFive {x : QuadraticAlgebra ℤ (-5) 0} : IsUnit x ↔ norm x = 1
```

An element of `QuadraticAlgebra ℤ (-5) 0` is a unit exactly when its norm
is `1`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L46) (line 46).

### QuadraticAlgebra.irreducible_two_int_negFive

```lean
theorem QuadraticAlgebra.irreducible_two_int_negFive : Irreducible 2
```

The embedded integer `2` is irreducible in
`QuadraticAlgebra ℤ (-5) 0`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L74) (line 74).

### QuadraticAlgebra.not_prime_two_int_negFive

```lean
theorem QuadraticAlgebra.not_prime_two_int_negFive : ¬Prime 2
```

The embedded integer `2` is not prime in
`QuadraticAlgebra ℤ (-5) 0`.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L130) (line 130).

<a id="qa-minus-five-not-ufd" name="qa-minus-five-not-ufd"></a>

### QuadraticAlgebra.not_uniqueFactorizationMonoid_int_negFive

```lean
theorem QuadraticAlgebra.not_uniqueFactorizationMonoid_int_negFive : ¬UniqueFactorizationMonoid (QuadraticAlgebra ℤ (-5) 0)
```

The integer quadratic algebra `QuadraticAlgebra ℤ (-5) 0` is not a unique
factorization monoid. The norm and factorization argument is motivated by
Vakil, *The Rising Sea*, Exercise 5.4.K.

[Source](../QuadraticAlgebras/SqrtNegFive.lean#L144) (line 144).

## Module `QuadraticAlgebras.NumberField`

> # Number fields from integer quadratic algebras
>
> This file connects the coordinate model `QuadraticAlgebra ℤ a b` to the
> number-field API.  It also records the elementary degree, discriminant,
> signature, and Minkowski-bound computations for `ℤ[√-5]`.
>
> The separate `QuadraticAlgebras.ClassNumberNegFive` module builds on these
> results to classify the ideals of norm at most two and compute the class number.
>
> ## References
>
> * Mathlib's [number-field class-number formalization](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/NumberTheory/NumberField/ClassNumber.lean)
>   by Anne Baanen, Riccardo Brasca and Xavier Roblot supplies
>   `NumberField.exists_ideal_in_class_of_norm_le`. The discriminant, bound
>   computation and norm-two specialization are assembled in this library.

[Module source](../QuadraticAlgebras/NumberField.lean)

### QuadraticAlgebra.mapCoeffsEquiv

```lean
def QuadraticAlgebra.mapCoeffsEquiv {S : Type u_1} {T : Type u_2} [CommRing S] [CommRing T] (e : S ≃+* T) (a b : S) : QuadraticAlgebra S a b ≃+* QuadraticAlgebra T (e a) (e b)
```

Transport a quadratic algebra along a ring equivalence of its
coefficients.

[Source](../QuadraticAlgebras/NumberField.lean#L38) (line 38).

### QuadraticAlgebra.mapCoeffsEquivOfEq

```lean
def QuadraticAlgebra.mapCoeffsEquivOfEq {S : Type u_1} {T : Type u_2} [CommRing S] [CommRing T] (e : S ≃+* T) {a b : S} (a' b' : T) (ha : e a = a') (hb : e b = b') : QuadraticAlgebra S a b ≃+* QuadraticAlgebra T a' b'
```

Transport a quadratic algebra along a ring equivalence, with the target
coefficients presented by equalities.

[Source](../QuadraticAlgebras/NumberField.lean#L51) (line 51).

### QuadraticAlgebra.numberField_fractionRing

```lean
instance QuadraticAlgebra.numberField_fractionRing (a b : ℤ) [IsDomain (QuadraticAlgebra ℤ a b)] : NumberField (FractionRing (QuadraticAlgebra ℤ a b))
```

The fraction field of a domain integer quadratic algebra is a number
field.

[Source](../QuadraticAlgebras/NumberField.lean#L63) (line 63).

### QuadraticAlgebra.ringOfIntegersEquiv

```lean
noncomputable def QuadraticAlgebra.ringOfIntegersEquiv (a b : ℤ) [IsDomain (QuadraticAlgebra ℤ a b)] [IsIntegrallyClosed (QuadraticAlgebra ℤ a b)] : QuadraticAlgebra ℤ a b ≃+* NumberField.RingOfIntegers (FractionRing (QuadraticAlgebra ℤ a b))
```

An integrally closed domain integer quadratic algebra is canonically the
ring of integers of its fraction field.

[Source](../QuadraticAlgebras/NumberField.lean#L81) (line 81).

### QuadraticAlgebra.SqrtNegFiveOrder

```lean
abbrev QuadraticAlgebra.SqrtNegFiveOrder : Type
```

The integer quadratic order `ℤ[√-5]`.

[Source](../QuadraticAlgebras/NumberField.lean#L97) (line 97).

### QuadraticAlgebra.SqrtNegFiveField

```lean
abbrev QuadraticAlgebra.SqrtNegFiveField : Type
```

The fraction field of `ℤ[√-5]`.

[Source](../QuadraticAlgebras/NumberField.lean#L100) (line 100).

### QuadraticAlgebra.instIsDomainSqrtNegFiveOrder

```lean
instance QuadraticAlgebra.instIsDomainSqrtNegFiveOrder : IsDomain SqrtNegFiveOrder
```

The integer order `ℤ[√-5]` is a domain, using `-5 ≡ 3 mod 4`.

[Source](../QuadraticAlgebras/NumberField.lean#L103) (line 103).

### QuadraticAlgebra.instIsIntegrallyClosedSqrtNegFiveOrder

```lean
instance QuadraticAlgebra.instIsIntegrallyClosedSqrtNegFiveOrder : IsIntegrallyClosed SqrtNegFiveOrder
```

Squarefreeness of `-5` and its remainder modulo four make `ℤ[√-5]`
integrally closed. This is a global instance for the specified order.

[Source](../QuadraticAlgebras/NumberField.lean#L107) (line 107).

<a id="qa-minus-five-ring-of-integers" name="qa-minus-five-ring-of-integers"></a>

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersEquiv

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersEquiv : SqrtNegFiveOrder ≃+* NumberField.RingOfIntegers SqrtNegFiveField
```

The canonical identification of `ℤ[√-5]` with the ring of integers of its
fraction field.

[Source](../QuadraticAlgebras/NumberField.lean#L114) (line 114).

### QuadraticAlgebra.algebraTrace_eq_trace_sqrtNegFive

```lean
theorem QuadraticAlgebra.algebraTrace_eq_trace_sqrtNegFive (x : SqrtNegFiveOrder) : (Algebra.trace ℤ SqrtNegFiveOrder) x = trace x
```

On `ℤ[√-5]`, algebra trace agrees with quadratic-algebra trace.

[Source](../QuadraticAlgebras/NumberField.lean#L121) (line 121).

### QuadraticAlgebra.discr_sqrtNegFiveOrder_basis

```lean
theorem QuadraticAlgebra.discr_sqrtNegFiveOrder_basis : Algebra.discr ℤ ⇑(basis (-5) 0) = -20
```

The standard basis of `ℤ[√-5]` has discriminant `-20`.

[Source](../QuadraticAlgebras/NumberField.lean#L129) (line 129).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersBasis

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersBasis : Module.Basis (Fin 2) ℤ (NumberField.RingOfIntegers SqrtNegFiveField)
```

The integral basis of the number field induced by the standard basis of
`ℤ[√-5]`.

[Source](../QuadraticAlgebras/NumberField.lean#L136) (line 136).

### QuadraticAlgebra.discr_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.discr_sqrtNegFiveField : NumberField.discr SqrtNegFiveField = -20
```

The number-field discriminant of `ℚ(√-5)` is `-20`.

[Source](../QuadraticAlgebras/NumberField.lean#L145) (line 145).

### QuadraticAlgebra.sqrtNegFiveFieldEquivRatQuadratic

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveFieldEquivRatQuadratic : SqrtNegFiveField ≃ₐ[ℚ] QuadraticAlgebra ℚ (-5) 0
```

The fraction field of `ℤ[√-5]` as the corresponding rational quadratic
algebra.

[Source](../QuadraticAlgebras/NumberField.lean#L157) (line 157).

### QuadraticAlgebra.finrank_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.finrank_sqrtNegFiveField : Module.finrank ℚ SqrtNegFiveField = 2
```

The degree of `ℚ(√-5)` over `ℚ` is two.

[Source](../QuadraticAlgebras/NumberField.lean#L177) (line 177).

### QuadraticAlgebra.instIsTotallyComplexSqrtNegFiveField

```lean
instance QuadraticAlgebra.instIsTotallyComplexSqrtNegFiveField : NumberField.IsTotallyComplex SqrtNegFiveField
```

The field `ℚ(√-5)` is totally complex: a real embedding would send a square
to `-5`, contradicting nonnegativity of real squares.

[Source](../QuadraticAlgebras/NumberField.lean#L183) (line 183).

### QuadraticAlgebra.nrComplexPlaces_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.nrComplexPlaces_sqrtNegFiveField : NumberField.InfinitePlace.nrComplexPlaces SqrtNegFiveField = 1
```

The number field `ℚ(√-5)` has exactly one complex place.

[Source](../QuadraticAlgebras/NumberField.lean#L200) (line 200).

### QuadraticAlgebra.classGroup_minkowskiBound_sqrtNegFiveField_lt_three

```lean
theorem QuadraticAlgebra.classGroup_minkowskiBound_sqrtNegFiveField_lt_three : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces SqrtNegFiveField * (↑(Module.finrank ℚ SqrtNegFiveField).factorial / ↑(Module.finrank ℚ SqrtNegFiveField) ^ Module.finrank ℚ SqrtNegFiveField * √|↑(NumberField.discr SqrtNegFiveField)|) < 3
```

The explicit Minkowski bound for ideal-class representatives in
`ℚ(√-5)` is strictly less than three.

[Source](../QuadraticAlgebras/NumberField.lean#L209) (line 209).

### QuadraticAlgebra.exists_ideal_in_class_of_absNorm_le_two

```lean
theorem QuadraticAlgebra.exists_ideal_in_class_of_absNorm_le_two (C : ClassGroup (NumberField.RingOfIntegers SqrtNegFiveField)) : ∃ (I : ↥(nonZeroDivisors (Ideal (NumberField.RingOfIntegers SqrtNegFiveField)))), ClassGroup.mk0 I = C ∧ Ideal.absNorm ↑I ≤ 2
```

Every ideal class of `ℚ(√-5)` has an integral representative of absolute
norm at most two. This applies Mathlib's prior formalization
`NumberField.exists_ideal_in_class_of_norm_le` (Anne Baanen, Riccardo Brasca
and Xavier Roblot) to the discriminant and Minkowski bound computed here.

[Source](../QuadraticAlgebras/NumberField.lean#L230) (line 230).

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
>
> ## References
>
> * Mathlib's [number-field class-number formalization](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/NumberTheory/NumberField/ClassNumber.lean)
>   by Anne Baanen, Riccardo Brasca and Xavier Roblot supplies the ideal-class
>   representative bound used through `QuadraticAlgebra.exists_ideal_in_class_of_absNorm_le_two`.
>   The norm-two ideal classification and class-number computation are local.
> * Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21,
>   2025 draft), Exercise 5.4.K, motivates the `√-5` example, not this
>   class-number calculation.

[Module source](../QuadraticAlgebras/ClassNumberNegFive.lean)

### QuadraticAlgebra.sqrtNegFiveModTwo

```lean
def QuadraticAlgebra.sqrtNegFiveModTwo : SqrtNegFiveOrder →+* ZMod 2
```

Reduction of `ℤ[√-5]` modulo the relation sending `√-5` to `1` in
`ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L42) (line 42).

### QuadraticAlgebra.sqrtNegFiveModTwo_surjective

```lean
theorem QuadraticAlgebra.sqrtNegFiveModTwo_surjective : Function.Surjective ⇑sqrtNegFiveModTwo
```

Reduction from `ℤ[√-5]` to `ZMod 2` is surjective.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L49) (line 49).

### QuadraticAlgebra.sqrtNegFiveIdealTwo

```lean
def QuadraticAlgebra.sqrtNegFiveIdealTwo : Ideal SqrtNegFiveOrder
```

The distinguished ideal of `ℤ[√-5]` obtained as the kernel of reduction
to `ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L54) (line 54).

### QuadraticAlgebra.quotientSqrtNegFiveIdealTwoEquiv

```lean
noncomputable def QuadraticAlgebra.quotientSqrtNegFiveIdealTwoEquiv : SqrtNegFiveOrder ⧸ sqrtNegFiveIdealTwo ≃+* ZMod 2
```

The quotient of `ℤ[√-5]` by its distinguished norm-two ideal is
`ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L60) (line 60).

### QuadraticAlgebra.instIsDedekindDomainSqrtNegFiveOrder

```lean
instance QuadraticAlgebra.instIsDedekindDomainSqrtNegFiveOrder : IsDedekindDomain SqrtNegFiveOrder
```

The integrally closed negative-five quadratic order is a Dedekind
domain.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L67) (line 67).

### QuadraticAlgebra.absNorm_sqrtNegFiveIdealTwo

```lean
theorem QuadraticAlgebra.absNorm_sqrtNegFiveIdealTwo : Ideal.absNorm sqrtNegFiveIdealTwo = 2
```

The distinguished ideal of `ℤ[√-5]` has absolute norm two.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L72) (line 72).

### QuadraticAlgebra.algebraNorm_eq_norm_sqrtNegFive

```lean
theorem QuadraticAlgebra.algebraNorm_eq_norm_sqrtNegFive (x : SqrtNegFiveOrder) : (Algebra.norm ℤ) x = norm x
```

On `ℤ[√-5]`, the algebra norm agrees with the quadratic-algebra norm.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L79) (line 79).

### QuadraticAlgebra.not_isPrincipal_sqrtNegFiveIdealTwo

```lean
theorem QuadraticAlgebra.not_isPrincipal_sqrtNegFiveIdealTwo : ¬Submodule.IsPrincipal sqrtNegFiveIdealTwo
```

The distinguished norm-two ideal of `ℤ[√-5]` is not principal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L86) (line 86).

### QuadraticAlgebra.eq_sqrtNegFiveIdealTwo_of_absNorm_eq_two

```lean
theorem QuadraticAlgebra.eq_sqrtNegFiveIdealTwo_of_absNorm_eq_two (I : Ideal SqrtNegFiveOrder) (hI : Ideal.absNorm I = 2) : I = sqrtNegFiveIdealTwo
```

Every ideal of `ℤ[√-5]` of absolute norm two is the distinguished kernel
ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L112) (line 112).

### QuadraticAlgebra.SqrtNegFiveRingOfIntegers

```lean
abbrev QuadraticAlgebra.SqrtNegFiveRingOfIntegers : Type
```

The ring of integers of `ℚ(√-5)`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L157) (line 157).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo : SqrtNegFiveRingOfIntegers →+* ZMod 2
```

Reduction of the ring of integers of `ℚ(√-5)` to `ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L161) (line 161).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo_surjective

```lean
theorem QuadraticAlgebra.sqrtNegFiveRingOfIntegersModTwo_surjective : Function.Surjective ⇑sqrtNegFiveRingOfIntegersModTwo
```

Reduction of the ring of integers of `ℚ(√-5)` to `ZMod 2` is
surjective.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L167) (line 167).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwo

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwo : Ideal SqrtNegFiveRingOfIntegers
```

The distinguished norm-two ideal in the ring of integers of `ℚ(√-5)`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L174) (line 174).

### QuadraticAlgebra.quotientSqrtNegFiveRingOfIntegersIdealTwoEquiv

```lean
noncomputable def QuadraticAlgebra.quotientSqrtNegFiveRingOfIntegersIdealTwoEquiv : SqrtNegFiveRingOfIntegers ⧸ sqrtNegFiveRingOfIntegersIdealTwo ≃+* ZMod 2
```

The quotient of the ring of integers of `ℚ(√-5)` by its distinguished
norm-two ideal is `ZMod 2`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L180) (line 180).

### QuadraticAlgebra.absNorm_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.absNorm_sqrtNegFiveRingOfIntegersIdealTwo : Ideal.absNorm sqrtNegFiveRingOfIntegersIdealTwo = 2
```

The distinguished ideal in the ring of integers of `ℚ(√-5)` has absolute
norm two.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L188) (line 188).

### QuadraticAlgebra.comap_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.comap_sqrtNegFiveRingOfIntegersIdealTwo : Ideal.comap sqrtNegFiveRingOfIntegersEquiv.toRingHom sqrtNegFiveRingOfIntegersIdealTwo = sqrtNegFiveIdealTwo
```

Pulling back the distinguished ideal of the ring of integers recovers the
distinguished ideal of `ℤ[√-5]`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L196) (line 196).

### QuadraticAlgebra.not_isPrincipal_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.not_isPrincipal_sqrtNegFiveRingOfIntegersIdealTwo : ¬Submodule.IsPrincipal sqrtNegFiveRingOfIntegersIdealTwo
```

The distinguished norm-two ideal in the ring of integers of `ℚ(√-5)` is
not principal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L206) (line 206).

### QuadraticAlgebra.ringHom_eq_sqrtNegFiveRingOfIntegersModTwo

```lean
theorem QuadraticAlgebra.ringHom_eq_sqrtNegFiveRingOfIntegersModTwo (f : SqrtNegFiveRingOfIntegers →+* ZMod 2) : f = sqrtNegFiveRingOfIntegersModTwo
```

Every ring homomorphism from the ring of integers of `ℚ(√-5)` to
`ZMod 2` is the distinguished reduction map.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L222) (line 222).

### QuadraticAlgebra.eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_eq_two

```lean
theorem QuadraticAlgebra.eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_eq_two (I : Ideal SqrtNegFiveRingOfIntegers) (hI : Ideal.absNorm I = 2) : I = sqrtNegFiveRingOfIntegersIdealTwo
```

Every ideal of absolute norm two in the ring of integers of `ℚ(√-5)` is
the distinguished kernel ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L250) (line 250).

### QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwoNonzero

```lean
noncomputable def QuadraticAlgebra.sqrtNegFiveRingOfIntegersIdealTwoNonzero : ↥(nonZeroDivisors (Ideal SqrtNegFiveRingOfIntegers))
```

The distinguished norm-two ideal, packaged as a nonzero ideal for the
class-group API.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L281) (line 281).

### QuadraticAlgebra.eq_top_or_eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_le_two

```lean
theorem QuadraticAlgebra.eq_top_or_eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_le_two (I : ↥(nonZeroDivisors (Ideal SqrtNegFiveRingOfIntegers))) (hI : Ideal.absNorm ↑I ≤ 2) : ↑I = ⊤ ∨ ↑I = sqrtNegFiveRingOfIntegersIdealTwo
```

A nonzero ideal of absolute norm at most two in the ring of integers of
`ℚ(√-5)` is either the unit ideal or the distinguished norm-two ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L293) (line 293).

### QuadraticAlgebra.classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo

```lean
theorem QuadraticAlgebra.classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo (C : ClassGroup SqrtNegFiveRingOfIntegers) : C = 1 ∨ C = ClassGroup.mk0 sqrtNegFiveRingOfIntegersIdealTwoNonzero
```

Every ideal class of `ℚ(√-5)` is either trivial or represented by the
distinguished norm-two ideal.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L311) (line 311).

<a id="qa-minus-five-class-number" name="qa-minus-five-class-number"></a>

### QuadraticAlgebra.classNumber_sqrtNegFiveField

```lean
theorem QuadraticAlgebra.classNumber_sqrtNegFiveField : NumberField.classNumber SqrtNegFiveField = 2
```

The class number of `ℚ(√-5)` is two. The local ideal classification
combines with Mathlib's ideal-class representative bound (Anne Baanen, Riccardo
Brasca and Xavier Roblot) specialized in `NumberField.lean`.

[Source](../QuadraticAlgebras/ClassNumberNegFive.lean#L330) (line 330).

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
