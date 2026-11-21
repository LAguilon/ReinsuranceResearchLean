# Bounded claims on `[0, M]` — regime partition and dual certificates (Stage B)

Status: **`PARTIAL`** — the four regimes below are numerically mapped and the
certificates are exact. The interior regime (R2) is **kernel-checked** in
`Research/StopLossBounded.lean` (`stopLoss_bound_interior`, plus the rational
sharpness witness `interior_sharp`), so R2 is `REPRODUCED`. R1 has *no* quadratic
certificate (proved below); R3/R4 are boundary-contact cases whose certificates are
derived but not yet formalised.
Track A, Issue #4. Date: 2026-11-21.

## 1. Problem

For `X ∈ [0, M]` with `E[X] = μ`, `E[X²] = m₂ = μ² + σ²`, and retention `d ∈ [0, M]`:

  `V* = sup E[(X - d)⁺]`  over all such laws.

Admissible parameter domain (hypothesis freeze): `0 < μ < M`,
`0 ≤ σ² ≤ μ(M - μ)`, `0 ≤ d ≤ M`. No other assumption is used.

## 2. Reduction to one parameter

Every two-atom law `{a, b}`, `a < b`, with these moments satisfies the classical
identity

  `(μ - a)(b - μ) = σ²`.                                              (2.1)

Putting `s := μ - a ∈ (0, μ]` gives

  `a = μ - s`,  `b = μ + σ²/s`,  `p_b = s²/(s² + σ²)`.                 (2.2)

For `a ≤ d ≤ b` the objective is `V(s) = p_b (b - d)`, and

  `V'(s) ∝ σ² (σ² + 2(μ - d)s - s²)`,                                 (2.3)

so the unconstrained maximiser is

  `s* = (μ - d) + √((μ - d)² + σ²)`,                                   (2.4)

equivalently `a* = d - √((μ-d)²+σ²)`, `b* = d + √((μ-d)²+σ²)` — the symmetric
pair around the retention. The admissible `s` is `[σ²/(M-μ), μ]`; clamping `s*` to
that interval produces the four regimes below.

## 3. Regime partition

| Regime | Condition | Extremal law | Value |
|---|---|---|---|
| **R1** kink | `d ≤ μ` and `σ² ≤ (μ-d)(M-μ)` | `{d, b}` with `b = μ + σ²/(μ-d)` | `μ - d` |
| **R2** interior | `s* ≤ d` and `d + s* ≤ M` | `{d - s*, d + s*}` | `(μ - d + s*)/2` |
| **R3** `a = 0` binds | `s* > d` | `{0, m₂/μ}` | `μ(1 - d/b₀)`, `b₀ = m₂/μ` |
| **R4** `b = M` binds | `s* > M - d` | `{a₁, M}`, `a₁ = (μM - m₂)/(M-μ)` | `q(M - d)`, `q = (μ-a₁)/(M-a₁)` |

The answer is `V* = max{R1, R2, R3, R4}`. In practice, as `d` increases at fixed
`(μ, σ²)` the maximiser moves R1 → R3 → R2 → R4, but R1 and R3 can coexist with
later regimes, which is why the theorem is stated as a maximum rather than as a
disjoint partition.

## 4. Certificates

All certificates are of the form: a quadratic `q` with `q ≥ (x-d)⁺` on `[0, M]`
and `E[q] = V` under the stated moments. Multiplying by `4s > 0` clears every
denominator.

### R2 — interior (the clean case)

  `q(x) = (x - a)² / (4s)`,  `a = d - s`,  `s² = (μ - d)² + σ²`.

Pointwise slack, with `b = d + s`:

* for `x ≤ d`: `q(x) = (x-a)²/(4s) ≥ 0 = (x-d)⁺`;
* for `x ≥ d`: `q(x) - (x - d) = (x - b)² / (4s) ≥ 0`.

Division-free form used by Lean (`4s` cleared):

  `4s·(x - d)⁺ ≤ (x - d + s)²`,  with slack `(x - d - s)²`.            (4.1)

Expectation, using `E[X] = μ` and `E[X²] = μ² + σ²`:

  `E[q] = [(μ - d + s)² + σ²] / (4s) = (μ - d + s)/2`.                 (4.2)

Equality holds for the two-atom law at `a` and `b` with weight `(μ-a)/(b-a)` at
`b`, which lies in `[0, M]` exactly when `s ≤ d` and `d + s ≤ M`.

### R3 — `a = 0` binds

  `q(x) = (d/b₀²)x² + (1 - 2d/b₀)x`,  `b₀ = m₂/μ`,

with slack `q(x) - (x-d) = d(x - b₀)²/b₀² ≥ 0`, and `q(0) = 0`, `q ≥ 0` on
`[0, d]` because `q'(0) = 1 - 2d/b₀ ≥ 0` in this regime. Then
`E[q] = μ(1 - d/b₀)`.

### R4 — `b = M` binds

  `q(x) = c(x - a₁)²`,  `c = (M - d)/(M - a₁)²`,  `a₁ = (μM - m₂)/(M - μ)`,

with slack `q(x) - (x-d) = c(M - x)(r - x)` where `r = 2a₁ + 1/c - M ≥ M`, so both
factors are non-negative on `[d, M]`. This is the "boundary term" case: the
non-negativity comes from `M - x ≥ 0` and `r - x ≥ 0`, not from a square.

### R1 — the kink regime has no quadratic certificate

**Proposition.** If `σ² ≤ (μ-d)(M-μ)` and `d ≤ μ`, then `V* = μ - d`, but no
quadratic `q` satisfies both `q ≥ (x-d)⁺` on `[0, M]` and `E[q] = μ - d`.

*Proof.* `(X-d)⁺ ≤ X - d` pointwise, so `V* ≤ μ - d`; the law `{d, b}` with
`b = μ + σ²/(μ-d) ≤ M` attains it, hence `V* = μ - d`. Suppose a quadratic `q`
attains equality. Since `E[q] - E[(X-d)⁺] = ∫ (q - (x-d)⁺) dP` is a non-negative
integral of a non-negative integrand, equality forces `q = (x-d)⁺` on the support
`{d, b}`, so `q(d) = 0`. Then `q ≥ 0` on `[0, d]` with `q(d) = 0` makes `d` an
interior minimum, so `q'(d) = 0` and `q(x) = c(x-d)²`. From `q(b) = b - d` we get
`c = 1/(b-d)`, and then for `x ∈ (d, b)`,
`q(x) = (x-d)²/(b-d) < x - d`, contradicting `q ≥ (x-d)⁺`. ∎

Numerically the best quadratic dual in R1 is strictly above the primal: for
`μ = 1/2`, `σ² = 1/100`, `d = 3/10`, `M = 1` the primal is `1/5` and the best
quadratic dual found is `0.21180…`, a gap of `1.18·10⁻²` that does not shrink
under refinement (the interpolation grid is refined to `10⁻⁴`).

This is why Stage C formalises R2 only: R1 needs the pointwise argument, not a
quadratic certificate, and R3/R4 need boundary terms that are not squares.

## 5. Worked example (rational, for Stage C)

`M = 1`, `μ = 1/2`, `σ² = 1/16`, `d = 1/2`. Then `s = √(0 + 1/16) = 1/4`,
`a = 1/4`, `b = 3/4`, and R2 applies (`s ≤ d`, `d + s ≤ 1`).

  `V* = (μ - d + s)/2 = (0 + 1/4)/2 = 1/8`,

attained by `{1/4, 3/4}` with mass `1/2` each: mean `1/2`, variance `1/16`,
value `(1/2)(1/4) = 1/8`. Certificate:

  `q(x) = (x - 1/4)²`,  `q(x) - (x - 1/2) = (x - 3/4)²`  for `x ≥ 1/2`.

## 6. Numerical evidence (Stage A)

`experiments/bounded_stoploss_check.py` evaluates the four closed forms and
compares them with an exhaustive three-atom primal on a grid of step `M/160`,
over `μ ∈ {0.2, 0.35, 0.5, 0.65, 0.8}`, `σ²/μ(M-μ) ∈ {0.1, 0.4, 0.7, 0.95}` and
`d ∈ {0, 0.15, …, 0.9}` (140 configurations). The closed form is never below the
enumerated primal (worst difference `-1.1·10⁻¹³`) and exceeds it by at most the
grid error (`~10⁻⁵`). The dual certificates for R2, R3 and R4 were checked by
dense sampling: worst violations `0`, `5·10⁻⁷`, `10⁻⁶` respectively, i.e. at
float noise.

## 7. What is not claimed

* The four-regime list is not proved exhaustive. It is supported by the
  one-parameter reduction (2.2)–(2.4), which is a proof that *every two-atom law*
  is covered, and by the Stage A enumeration, which found no better three-atom
  law. Exhaustiveness over general laws is `CONJECTURED`.
* R1's impossibility statement is proved for quadratics only; the true dual over
  all continuous majorants is attained, and its extremal majorant is piecewise
  linear, not quadratic.
* No novelty claim. The mean/variance stop-loss literature (De Vylder–Goovaerts–
  De Pril 1982; Jansen–Haezendonck–Goovaerts 1986; Heijnen 1990) covers the
  bounded-range problem; this note reproduces the technique with an explicit
  certificate and a regime map.
