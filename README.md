# ReinsuranceResearchLean — insurance mathematics, formally verified

Lean 4 + Mathlib formalisation of extremal results in insurance mathematics.

* **Track B — dependence uncertainty.** Extremal risk aggregation with known
  marginals and unknown dependence. Pilot: the two-point (Bernoulli) case, where
  the coupling set is a segment and the optimisation over dependence is exactly
  solvable.
* **Track A — ruin theory / Schmitter problem.** Entry point: stop-loss bounds
  under mean and variance constraints, proved by an explicit dual certificate.

## Status of every result

| Result | File | Tag |
|---|---|---|
| Feasible couplings of two Bernoulli risks form the interval `[max 0 (p+q-1), min p q]` | `Research/Bernoulli.lean` | `REPRODUCED` |
| Comonotone coupling maximises / countermonotone minimises `E[φ(X+Y)]` for convex `φ` | `Research/Bernoulli.lean` | `REPRODUCED` |
| `E[(X-d)⁺] ≤ μ - d/2` when `Var X = μ²`, `0 ≤ d ≤ μ` | `Research/StopLoss.lean` | `REPRODUCED` |
| Bounded claims `[0,M]`, interior case: `E[(X-d)⁺] ≤ (μ-d+r)/2`, `r² = (μ-d)²+σ²` | `Research/StopLossBounded.lean` | `REPRODUCED` |
| Bounded claims `[0,M]`, case `a=0`: `E[(X-d)⁺] ≤ μ(1-d/b₀)` | `Research/StopLossBounded.lean` | `REPRODUCED` |
| Bounded claims `[0,M]`, case `b=M`: `E[(X-d)⁺] ≤ (M-d)(μ-a₁)/(M-a₁)` | `Research/StopLossBounded.lean` | `REPRODUCED` |
| Bounded claims `[0,M]`: unified clamped theorem over the whole domain | — | `PARTIAL` |

Nothing here is claimed as novel. `LITERATURE.md` records the audit, its date and
its limits (no keyword-search access; fetch-only citation verification).

**Sharpness caveat for the Schmitter problem.** The pointwise stop-loss envelope
is attained by a *different* extremal law at each retention `d`, so substituting it
into stop-loss monotonicity of the ruin probability gives a **valid upper bound**
on `sup ψ(u)`, **not** the sharp Schmitter supremum. See
`research/trackA-stop-loss-bounds.md` §10a.

## Contents

| Path | What it is |
|---|---|
| `Research/Bernoulli.lean` | Couplings of two Bernoulli risks; feasible interval; convex-order monotonicity; extremal couplings |
| `Research/StopLoss.lean` | Stop-loss bound under `E[X]=μ`, `Var X = μ²`; quadratic dual certificate; two-point extremal law |
| `Research/StopLossBounded.lean` | Interior (R2) bounded-claims bound with perfect-square certificate, plus a rational sharpness witness |
| `Research/Verify.lean` | Imports every public module, prints the axiom footprint of each theorem, and instantiates the main bound at concrete data (non-vacuity) |
| `research/trackB-dependence-uncertainty.md` | Track B research note |
| `research/trackA-stop-loss-bounds.md` | Track A research note, with the sharpness caveat |
| `research/trackA-bounded.md` | Bounded-claims supremum, three certificate cases, and the errata removing the phantom `μ-d` regime |
| `LITERATURE.md` | Audited references with DOIs and status labels |
| `experiments/bernoulli_check.py` | Exact-rational verification of the Track B claims, plus a three-point exploration |
| `experiments/bounded_stoploss_check.py` | Stage A for bounded claims: closed-form candidates versus enumerated primal |
| `AGENTS.md` | Binding research and formalisation rules |

## Headline statements (kernel-checked)

```lean
theorem Coupling.expCost_le_comonotone
    (φ : ℚ → ℚ) {p q : ℚ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1) (hconv : 0 ≤ φ 2 - 2 * φ 1 + φ 0)
    (h : Coupling p q t) :
    expCost φ p q t ≤ expCost φ p q (min p q)

theorem Research.stopLoss_bound (L : FinLaw ι) (X : ι → ℚ) {μ d : ℚ} (hμ : 0 < μ)
    (hd : 0 ≤ d) (hdμ : d ≤ μ) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = 2 * μ ^ 2) :
    L.stopLossExpectation X d ≤ μ - d / 2
```

`Research/Verify.lean` prints the axiom footprint of all nine theorems plus the
non-vacuity witness; CI fails unless every line is exactly
`[propext, Classical.choice, Quot.sound]`.

## Build

```bash
lake update          # Mathlib v4.36.0
lake exe cache get   # prebuilt oleans (~7 GB)
lake build           # 2 080 jobs, ~10 s after the cache
```

The library uses a **narrow import set** (rationals, `Finset`, big operators,
`linarith`/`nlinarith`/`positivity`/`ring`/`split_ifs`), not `import Mathlib`. That
cuts the build from 18 256 jobs to 2 080; adding a broad import again is a
regression and should be rejected in review.

## Run the experiments

```bash
python3 experiments/bernoulli_check.py
python3 experiments/bounded_stoploss_check.py
```
No third-party dependencies; exact rational arithmetic where it matters.

## How to contribute

Open an issue with the `research-question` or `counterexample` label. Every claim
carries one of `PROVED`, `REPRODUCED`, `PARTIAL`, `CONJECTURED`. Unproved
statements stay out of `Research/`. See `AGENTS.md` for the three-stage pipeline.

## Licence

Apache-2.0 (code). Documentation CC BY 4.0.
