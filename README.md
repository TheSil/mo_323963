# Integrality of the five-step product recurrence

This repository contains a mathematical proof and a complete Lean 4
formalization of the integrality problem from
[MathOverflow question 323963](https://mathoverflow.net/questions/323963).

The sequence is defined over the positive rationals by

```text
a(0) = a(1) = a(2) = a(3) = a(4) = 1
a(n+5) = (a(n+4)+1)(a(n+3)+1)(a(n+2)+1)(a(n+1)+1) / a(n)
```

Its first terms are

```text
1, 1, 1, 1, 1, 16, 136, 9316, 43398586, 941718655098991, ...
```

The result proved here is that every term is an integer.

## Proof outline

The proof shows that `a(n)` has nonnegative `p`-adic valuation at every
prime `p`. Odd primes and the prime `2` require different arguments.

* **Odd primes.** Put `b(n) = a(n) + 1` and introduce valuation atoms
  `t(n)` satisfying

  ```text
  v_p(b(n+5)) = t(n+5) + t(n).
  ```

  A simultaneous induction proves that all atoms are nonnegative and that
  every positive atom is preceded by four zero atoms. This confinement,
  together with

  ```text
  v_p(a(n+5)) = t(n+1) + t(n+2) + t(n+3) + t(n+4),
  ```

  gives `v_p(a(n)) >= 0` for every odd prime.

* **The prime 2.** An alternating first integral is used to transform the
  original sequence into a sequence `x(n)`. A four-term `2`-adic tube for
  `x` returns to itself after 14 steps. The actual valuations need not be
  periodic; instead, the return supplies the periodic lower-bound word

  ```text
  0, 0, 0, 4, 0, 4, 2, 2, -2, 2, 2, 4, 0, 4.
  ```

  The original terms are recovered from pairs of transformed terms:

  ```text
  a(n+2) = x(n)x(n+2) / K(n),
  K(n) = 1 for even n and 16 for odd n.
  ```

  Pairing the lower bounds two positions apart makes the single `-2`
  harmless and proves `v_2(a(n)) >= 0`.

Since a rational number with nonnegative valuation at every prime has
denominator `1`, all terms are integers.

## Contents

* [Proof.lean](Proof.lean) — the complete, self-contained Lean 4 + Mathlib
  formalization. It contains no `sorry`. The final theorem, in namespace
  `MO323963`, is

  ```lean
  theorem integrality (n : ℕ) : ∃ z : ℤ, a n = z
  ```

* [proof.tex](proof.tex) — the mathematical exposition.
* [proof.pdf](proof.pdf) — the rendered exposition.

## Verification

The project uses Lean `v4.29.0` and the corresponding Mathlib release.

```text
lake exe cache get
lake build
```

The build checks the complete proof with the Lean kernel.
