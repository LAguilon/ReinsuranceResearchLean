# ReinsuranceResearchLean — insurance mathematics, formally verified

## Status: closed experiment (2026-11-21)

This repository is a **closed experiment**, not an active project. Read this section
before anything else.

**What is machine-checked.** 44 declarations in Lean 4.36.0 + Mathlib, zero `sorry`,
zero custom axioms, every footprint exactly `propext, Classical.choice, Quot.sound`.
The 11 that carry mathematical content:

| Statement | Tag |
|---|---|
| Two Bernoulli couplings are feasible iff `max 0 (p+q-1) ≤ t ≤ min p q` | REPRODUCED |
| Comonotone maximises / countermonotone minimises `E[φ(X+Y)]` for convex `φ` | REPRODUCED |
| `E[(X−d)⁺] ≤ μ − d/2` when `Var X = μ²`, `0 ≤ d ≤ μ` | REPRODUCED |
| Bounded `[0,M]`: three case bounds (interior, `a=0`, `b=M`) | REPRODUCED |
| Bounded `[0,M]`: unified `stopLoss_bound_bounded` over the closed domain | REPRODUCED |
| Unbounded `[0,∞)`: `stopLoss_bound_unbounded`, general `σ²` | REPRODUCED |
| `σ² = 0 ⇒ E[(X−d)⁺] = (μ−d)⁺` | REPRODUCED |
| `f` is maximised at `s*` (clamp lemma) | REPRODUCED |

**What is classical.** All of it. The mean/variance stop-loss bounds are due to
De Vylder–Goovaerts–De Pril (1982), Jansen–Haezendonck–Goovaerts (1986), Heijnen
(1990), Genest–Marceau–Mesfioui (2002); the dependence-uncertainty results to
Embrechts–Puccetti–Rüschendorf (2013) and Puccetti–Wang–Wang (2013). Citations are
metadata-verified only (Crossref/OpenAlex); **no paper was read**. See `LEDGER.md`
for the exact searches and `LITERATURE.md` for the DOIs.

**What was wrong, and corrected.** (1) A "kink regime" claiming `sup = μ − d` was
a phantom: `(x−d)⁺ ≥ x−d`, so `μ−d` is Jensen's *lower* bound. (2) The interior
certificate uses `r = √((μ−d)²+σ²)`, not `s* = (μ−d)+r`; conflating them produced
two failed assemblies. (3) Prose said bounds hold for "every law" while the Lean
statements are finite-support. (4) A claimed ruin identity
`ψ(u) = (λ/c)E[(X_I−u)⁺]` is false in general — it is the first term of the renewal
equation (see Issue #2).

**What is NOT shown.** No ruin probability is formalised in Lean. The Schmitter
problem is not solved. The stop-loss *envelope* is a valid but **non-sharp** upper
bound on `sup ψ`. The measure-theoretic version of the bound is **not** completed
(`Research/Measure/StopLossMeasure.lean` proves only the pointwise majorant).
Nothing here is novel, and no claim of novelty is made anywhere.

**Verify in one command.**

```bash
lake exe cache get && lake build && lake env lean Research/Verify.lean
```

The last command prints 44 lines; CI fails unless every one is exactly
`[propext, Classical.choice, Quot.sound]`.


## Fidelity table — what the formal statement does and does not say

| Formal statement (Lean) | Prose claim this licenses | Not claimed |
|---|---|---|
| `integral_stopLoss_le`: `[IsProbabilityMeasure P]`, `MemLp X 2 P`, `0 < s`, `s² = (μ−d)²+σ²`, `∫X = μ`, `∫X² = μ²+σ²` ⟹ `∫ (X−d)⁺ ≤ (μ−d+s)/2` | "the interior mean/variance stop-loss bound holds for arbitrary distributions on a probability space, not only finitely supported ones" | no `X ≥ 0` hypothesis; no upper bound `M`; **not** a supremum — any admissible `s` gives a bound; no sharpness in the insurance class |
| `interior_majorant_all`: `4s(x−d)⁺ ≤ (x−d+s)²` for all real `x`, `s > 0` | "the pointwise certificate needs no support assumption" | nothing about integration |

**Attainment caveat.** The measure-theoretic bound is attained exactly by the
two-atom law `{d−r, d+r}` with `r = √((μ−d)²+σ²)`. For `μ=1, σ²=1, d=0.5` that law is
`{−0.618034, 1.618034}` with masses `0.276393 / 0.723607`; it reproduces mean `1`,
second moment `2`, and `E[(X−d)⁺] = 0.809016994 = (μ−d+r)/2` to machine precision.
Because the lower atom is **negative**, this law is outside the insurance class
`X ≥ 0`, where the supremum is the smaller `0.75`. The measure-theoretic theorem
therefore says nothing about `X ≥ 0`.

## Contents of the audit

| Group | Count | Names |
|---|---|---|
| Content | 11 | `Coupling.iff`, `Coupling.expCost_le_comonotone`, `Coupling.countermonotone_le_expCost`, `stopLoss_bound`, `stopLoss_bound_interior`, `stopLoss_bound_atom_zero`, `stopLoss_bound_atom_top`, `stopLoss_bound_bounded`, `stopLoss_bound_unbounded`, `stopLoss_variance_zero`, `f_le_clamp` |
| Witnesses | 4 | `twoPoint_attains`, `interior_sharp`, `atomZero_sharp`, `atomTop_sharp` |
| Helpers | 29 | `cells_nonneg`, `cells_sum`, `Coupling.convex`, `expCost_affine`, `expCost_mono`, `comonotone_feasible`, `countermonotone_feasible`, `stopLoss_convex`, `stopLoss_majorant`, `sum_quadratic` (ℚ, ℝ), `sum_quadratic_const` (ℚ, ℝ), `interior_majorant` (ℚ, ℝ), `atomZero_majorant` (ℚ, ℝ), `atomTop_majorant` (ℚ, ℝ), `sStar_sq`, `sStar_gt`, `sStar_pos`, `sStar_sub_A_nonneg`, `two_mul_le_sStar`, `f_diff_num`, `f_inc`, `f_dec`, `f_sStar`, `f_mu`, `f_lo`, `coverage_atom_zero`, `coverage_atom_top`, `stopLoss_bound_nonvacuous`, `bound_interior_branch`, `bound_atom_zero_branch`, `bound_atom_top_branch`, `bound_unbounded_interior`, `bound_unbounded_atom_zero` |

(The helper row lists 29 distinct statements; several appear twice, once over `ℚ`
and once over `ℝ`, and are counted once in the 44.)

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
| Bounded claims `[0,M]`: unified `stopLoss_bound_bounded` over the full closed domain | `Research/StopLoss/BoundedUnified.lean` | `REPRODUCED` |
| Unbounded `[0,∞)`, general `σ²`: `stopLoss_bound_unbounded` | `Research/StopLoss/GeneralVar.lean` | `REPRODUCED` |

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

`Research/Verify.lean` prints the axiom footprint of all **44** audited declarations
(11 content theorems, 4 sharpness witnesses, 29 algebra helpers — the count is a
build-health metric, not a research metric) plus the non-vacuity witness; CI fails unless every line is exactly
`[propext, Classical.choice, Quot.sound]`.

## Build

```bash
lake update          # Mathlib v4.36.0
lake exe cache get   # prebuilt oleans (~7 GB)
lake build           # 3 140 jobs, ~2 s incremental after the cache
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
