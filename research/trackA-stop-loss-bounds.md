# Research note — sharp stop-loss bounds under mean and variance constraints

Status: **`REPRODUCED`** for the constant-variance-ratio case; the general
variance case is **`PARTIAL`** (see §10). Track A entry point, 2026-11-21.
Lean: 4.36.0 + Mathlib `v4.36.0`.

## 1. The mathematical problem

Among claim-size distributions `X ≥ 0` with prescribed mean `μ` and variance `σ²`,
how large can the stop-loss transform `E[(X - d)⁺]` be at a given retention `d`?

## 2. Relevance to insurance and reinsurance

`E[(X-d)⁺]` is the expected cost of an excess-of-loss cover with retention `d`, so
this is the sharp upper price of a non-proportional layer when only the first two
moments of the claim size are known — the information an underwriter typically
has. Because ruin probabilities in the Cramér–Lundberg model are ordered by
stop-loss order, a bound of this type propagates to a bound on the ruin
probability. That propagation is the *mechanism* behind the Schmitter problem —
but see §10a: it yields a valid bound, not sharpness.

## 3. What was previously known

Moment-constrained stop-loss bounds are classical; Genest, Marceau and Mesfioui
(2002, *Upper stop-loss bounds for sums of possibly dependent risks with given
means and variances*, Statist. Probab. Lett. 57, 33–41,
`10.1016/s0167-7152(02)00039-1`) give upper stop-loss bounds under mean/variance
information. The Schmitter extremal problem and its partial solution are
Brockett–Goovaerts–Taylor (1991) and Kaas (1991); the randomised version is
Albrecher–Araujo-Acuña (2021). See `LITERATURE.md`.

## 4. What was investigated

The dual-certificate route rather than the primal optimisation: exhibit a
quadratic majorant of the payoff whose expectation is computable from `μ` and
`σ²`, then show the bound is attained. This is the standard route to sharp
moment bounds, but it has the advantage of producing a *machine-checkable
certificate*: a polynomial identity and a sign condition.

## 5. What was found

For the case `Var(X) = μ²` (coefficient of variation 1) and `0 ≤ d ≤ μ`:

  `E[(X - d)⁺] ≤ μ - d/2`,

with equality for the two-point law `{0, 2μ}` with mass `1/2` on each atom.

The certificate is the quadratic

  `q(x) = (1 - d/μ) x + d x² / (4 μ²)`,

which majorises `(x - d)⁺` on `[0, ∞)`. Below the kink `q ≥ 0` is immediate from
`d ≤ μ`; above the kink the excess is the exact square

  `q(x) - (x - d) = d (x - 2μ)² / (4 μ²) ≥ 0`.

Taking expectations and using `E[X] = μ`, `E[X²] = 2μ²` gives
`E[(X-d)⁺] ≤ (1-d/μ)μ + 2dμ²/(4μ²) = μ - d/2`. The perfect square is what makes
the constant sharp, and it also forces equality to concentrate mass at `0` and
`2μ`.

## 6. Formulation

`Research/StopLoss.lean`:

* `FinLaw ι` — non-negative weights on a finite type; `mean`, `secondMoment`,
  `stopLossExpectation`.
* `FinLaw.sum_quadratic` — `Σ mᵢ (a Xᵢ + b Xᵢ²) = a·mean + b·secondMoment`.
* `stopLoss_majorant` — the pointwise certificate in scaled form
  `4μ²(x-d)⁺ ≤ 4μ²x - 4μdx + dx²`.
* `stopLoss_bound` — the sharp bound for finite laws.
* `twoPoint_attains` — the two-point law `{0, 2μ}` attains it exactly.

## 7. Assumptions

* `X ≥ 0`, finite support, rational values — exact arithmetic, no measure theory.
* `0 < μ`, `0 ≤ d ≤ μ`.
* `E[X²] = 2μ²`, i.e. `σ = μ`. This is the boundary case in which a two-point
  extremal law suffices.
* The general-`σ` statement is **not** proven here (§10).

## 8. Proof strategy

Case split at the kink `x = d`; on the upper branch the gap between the majorant
and the payoff is a square, on the lower branch the majorant is non-negative
because `d ≤ μ`. Summing with non-negative weights and evaluating with the two
moment constraints leaves an inequality that is linear in `E[(X-d)⁺]`; division
by `4μ² > 0` finishes.

## 9. Lean implementation and verification

```
lake build            # 18256 jobs, green
#print axioms Research.stopLoss_bound   -- propext, Classical.choice, Quot.sound
```

`twoPoint_attains` is checked with `Bool`-indexed atoms so the two-point law is
literal data, not a hypothesis.

## 10a. What the envelope does *not* give (sharpness caveat)

The pointwise envelope `d ↦ sup E[(X-d)⁺]` is attained by a different extremal
law at each retention: `{0, 2μ}` for `d ≤ μ`, and a `d`-dependent two-point law
for `d > μ`. No single claim distribution attains the envelope simultaneously for
all `d ≥ 0`.

Consequently, substituting the envelope into stop-loss monotonicity of `ψ` gives a
**valid upper bound** on `sup ψ(u)`, but **not** the sharp Schmitter supremum.
Sharpness requires optimising over claim distributions *jointly across all
retentions*, which is the actual open problem. Any statement in this repository
that reads as "sharp ruin bound" is to be corrected on sight.

## 10. What remains unresolved

* **General variance.** For `σ² ≠ μ²` the extremal law is supported on three
  atoms `{0, y, z}` with `y < d < z`, and the dual majorant is a quadratic
  touching at three points. A closed form exists in the moment-problem literature
  (and the Genest–Marceau–Mesfioui bounds cover related statements), but this
  audit could not pin down the exact statement; recorded as `PARTIAL`, **not** as
  new mathematics.
* **From stop-loss to ruin.** Monotonicity of the ruin probability with respect to
  stop-loss order is classical but analytic (Laplace transforms, adjustment
  coefficient); nothing formalised.
* **Bounded claims.** Restricting support to `[0, M]` changes the extremal law at
  the boundary; a natural next formalisation target.
* **Randomised initial surplus** (Albrecher–Araujo-Acuña 2021) replaces the fixed
  surplus by a random variable and reformulates the problem in convex order; this
  is the cleanest route from the stop-loss bound above to a ruin-probability
  statement, and it is where the next Track A increment should go.
