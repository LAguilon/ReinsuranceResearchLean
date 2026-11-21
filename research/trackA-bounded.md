# Bounded claims on `[0, M]` — regime partition and dual certificates (Stage B)

Status: **`PARTIAL`** — all three certificate cases are kernel-checked in both
tiers: `Research/StopLossBounded.lean` (exact rational, with sharpness witnesses)
and `Research/StopLoss/BoundedReal.lean` (real, for composition). The real tier
also carries `f_inc`, `f_dec`, `f_le_clamp` (`Research/Real/Sqrt.lean`) and
`stopLoss_variance_zero`. What remains is the unified theorem over the clamped
formula. Track A, Issue #4. Date: 2026-11-21.

## 0. Errata (2026-11-21) — a phantom regime removed

An earlier version of this note listed a fourth "kink regime" (R1) with value
`μ - d`, claiming it was the supremum when `σ² ≤ (μ-d)(M-μ)`.

**That was wrong.** Since `(x - d)⁺ ≥ x - d` pointwise, `E[(X-d)⁺] ≥ μ - d`
always: `μ - d` is a **lower** bound (Jensen's inequality for the convex function
`x ↦ x⁺`), never an upper bound. It is attained only when `X ≥ d` almost surely,
which forces `σ² = 0` and `μ ≥ d`.

Concrete counterexample to the old claim: `M = 1`, `μ = 1/2`, `σ² = 1/100`,
`d = 3/10`. The old note asserted `sup = μ - d = 0.2`; the law
`{0.076393, 0.523607}` with mass `0.947214` on the upper atom has mean `1/2`,
variance `1/100`, and stop-loss expectation `0.211803 > 0.2`. So the supremum is
at least `0.211803`, and the "regime" was an artefact of taking a maximum over
candidate *formulas* instead of over valid *upper bounds*.

The corrected statement is a single clamped formula (§3), and the three
certificate cases are the three ways the clamp can bind.

## 1. Problem

For `X ∈ [0, M]` with `E[X] = μ`, `E[X²] = m₂ = μ² + σ²`, and `d ∈ [0, M]`:

  `V* = sup E[(X - d)⁺]`  over all such laws.

Domain (hypothesis freeze): `0 < μ < M`, `0 ≤ σ² ≤ μ(M - μ)`, `0 ≤ d ≤ M`.

## 2. Reduction to one parameter

Two-atom laws `{a, b}`, `a < b`, with these moments satisfy

  `(μ - a)(b - μ) = σ²`.                                              (2.1)

With `s := μ - a ∈ (0, μ]`:

  `a = μ - s`,  `b = μ + σ²/s`,  `p_b = s²/(s² + σ²)`,                 (2.2)

and for `a ≤ d ≤ b` the objective is

  `f(s) = (s²(μ - d) + sσ²)/(s² + σ²)`,   `f'(s) ∝ σ²(σ² + 2(μ-d)s - s²)`. (2.3)

So `f` increases up to

  `s* = (μ - d) + √((μ-d)² + σ²)`                                      (2.4)

and decreases after. Note `s* > μ - d` strictly whenever `σ² > 0` — this is the
precise sense in which the Jensen value `μ - d` is never the supremum.

## 3. The supremum

The admissible range is `s ∈ [σ²/(M-μ), μ]`: the lower end is the constraint
`b ≤ M`, the upper end is `a ≥ 0`. Hence

  `V* = f( s_c )`,   `s_c = clamp(s*, σ²/(M-μ), μ)`.                   (3.1)

Three cases, by which end of the clamp binds:

| Case | Condition | Extremal atoms | Value |
|---|---|---|---|
| **I** interior | `σ²/(M-μ) ≤ s* ≤ μ` | `a = μ - s*`, `b = μ + σ²/s*` | `(μ - d + r)/2`, `r = √((μ-d)²+σ²)` |
| **A** `a = 0` | `s* ≥ μ` | `{0, μ + σ²/μ}` | `f(μ)` |
| **B** `b = M` | `s* ≤ σ²/(M-μ)` | `{μ - s₀, M}`, `s₀ = σ²/(M-μ)` | `f(s₀)` |
| **D** degenerate | `σ² = 0` | `{μ}` | `max(μ - d, 0)` |

At the interior case the atoms are symmetric around `d`: writing
`r = √((μ-d)²+σ²)`, one checks `a = d - r` and `b = d + r` (because
`σ²/s* = r - (μ-d)`).

## 4. Certificates

Each case carries a quadratic `q` with `q ≥ (x-d)⁺` on `[0, M]` and `E[q] = V*`,
so the bound holds for **every** law with the stated moments, not only for
two-atom laws. Attainment by the two-atom law then gives equality.

### I — interior

  `q(x) = (x - a)²/(4r)`,  `a = d - r`,  `r = √((μ-d)²+σ²)`.

* `x ≤ d`: `q(x) ≥ 0 = (x-d)⁺`;
* `x ≥ d`: `q(x) - (x-d) = (x - b)²/(4r) ≥ 0`.

Division-free: `4r(x-d)⁺ ≤ (x-d+r)²`, slack `(x-d-r)²`.
`E[q] = [(μ-d+r)² + σ²]/(4r) = (μ-d+r)/2`.

### A — `a = 0`

  `q(x) = (d/b₀²)x² + (1 - 2d/b₀)x`,  `b₀ = m₂/μ = μ + σ²/μ`,

with `q(0) = 0` and slack `q(x) - (x-d) = d(x - b₀)²/b₀² ≥ 0`; on `[0, d]`,
`q ≥ 0` because `q'(0) = 1 - 2d/b₀ ≥ 0` in this case. `E[q] = μ(1 - d/b₀)`.

### B — `b = M`

  `q(x) = c(x - a₁)²`,  `c = (M-d)/(M-a₁)²`,  `a₁ = (μM - m₂)/(M-μ)`,

with slack `q(x) - (x-d) = c(M - x)(r₂ - x)`, `r₂ = 2a₁ + 1/c - M ≥ M`, so both
factors are non-negative on `[d, M]`. This is the boundary-term case.

### Why there is no fourth case

`μ - d` is not a supremum (see §0), and the clamp has only two ends. So the three
cases plus the degenerate `σ² = 0` exhaust the parameter space by construction —
no Carathéodory argument is needed, because each case's certificate already
covers *all* laws.

## 5. Worked example (rational, kernel-checked)

`M = 1`, `μ = 1/2`, `σ² = 1/16`, `d = 1/2`: `r = 1/4`, `a = 1/4`, `b = 3/4`,
`V* = 1/8`, attained by `{1/4, 3/4}` with mass `1/2` each. Certificate
`q(x) = (x - 1/4)²`, slack `(x - 3/4)²`. Formalised as
`Research.stopLoss_bound_interior` and `Research.interior_sharp`.

## 6. Numerical evidence (Stage A)

`experiments/bounded_stoploss_check.py` evaluates (3.1) against an exhaustive
three-atom primal on a grid of step `M/160`, over `μ ∈ {0.2, 0.35, 0.5, 0.65, 0.8}`,
`σ²/μ(M-μ) ∈ {0.1, 0.4, 0.7, 0.95}`, `d ∈ {0, 0.15, …, 0.9}` (140 configurations).
Largest deviation `1.5·10⁻⁵`, i.e. grid error; the closed form is never below the
enumerated primal beyond `10⁻¹³`. Adversarial gate (`σ² = 0`, `σ² = μ(M-μ)`,
`d = 0`, `d = M`, `d = μ`): PASS.

## 7. What is not claimed

* Cases A and B are kernel-checked as bounds with sharpness witnesses, and their
  real-tier ports exist, but the unified `stopLoss_bound_bounded` is not stated.
  Three concrete obstacles are now identified:
  1. the identities `f(clamp) = case formula` at the three endpoints;
  2. the coverage implications (`s* ≥ μ ⇒ b₀ ≥ 2d`, `s* ≤ lo ⇒ 2(M−d) ≤ M−μ+lo`);
  3. the degenerate `σ² = 0` branch, where `f A 0 s = A` can be negative while
     `E[(X−d)⁺] ≥ 0`, so the statement needs `max 0` there.
* The reduction (2.1)–(2.2) covers two-atom laws; the certificates are what lift
  the bound to arbitrary laws. Case I's certificate is formalised; A and B are not.
* No novelty claim: the mean/variance bounded-range literature (De Vylder–
  Goovaerts–De Pril 1982; Jansen–Haezendonck–Goovaerts 1986; Heijnen 1990) covers
  this problem. What is new here is only the explicit certificate bookkeeping.
