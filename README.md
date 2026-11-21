# ReinsuranceResearchLean — insurance mathematics, formally verified

Lean 4 + Mathlib formalisation of extremal results in insurance mathematics.

* **Track B — dependence uncertainty.** Extremal risk aggregation with known
  marginals and unknown dependence. Pilot: the two-point (Bernoulli) case, where
  the coupling set is a segment and the optimisation over dependence is exactly
  solvable.
* **Track A — ruin theory / Schmitter problem.** Entry point: sharp stop-loss
  bounds under mean and variance constraints, proved by an explicit dual
  certificate.

**Status labels: `REPRODUCED`** — classical results, independently formalised.
Nothing here is claimed as new; see `LITERATURE.md` for the audit and its limits.

## Contents

| Path | What it is |
|---|---|
| `Research/Bernoulli.lean` | Couplings of two Bernoulli risks; feasible interval; convex-order monotonicity; extremal couplings; axiom audit |
| `Research/StopLoss.lean` | Sharp stop-loss bound `E[(X-d)⁺] ≤ μ - d/2` under `E[X]=μ`, `Var X = μ²`; quadratic dual certificate; two-point extremal law |
| `research/trackB-dependence-uncertainty.md` | Track B research note |
| `research/trackA-stop-loss-bounds.md` | Track A research note |
| `LITERATURE.md` | Audited references with DOIs and status labels (audit date 2026-11-21) |
| `experiments/bernoulli_check.py` | Exact-rational verification of the formalised claims, plus the three-point exploration |

## Headline statements (kernel-checked)

```lean
theorem Coupling.expCost_le_comonotone
    (φ : ℚ → ℚ) {p q : ℚ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1) (hconv : 0 ≤ φ 2 - 2 * φ 1 + φ 0)
    (h : Coupling p q t) :
    expCost φ p q t ≤ expCost φ p q (min p q)

theorem Coupling.countermonotone_le_expCost
    (φ : ℚ → ℚ) {p q t : ℚ} (hconv : 0 ≤ φ 2 - 2 * φ 1 + φ 0) (h : Coupling p q t) :
    expCost φ p q (max 0 (p + q - 1)) ≤ expCost φ p q t
```

and, for the stop-loss development:

```lean
theorem Research.stopLoss_bound (L : FinLaw ι) (X : ι → ℚ) {μ d : ℚ} (hμ : 0 < μ)
    (hd : 0 ≤ d) (hdμ : d ≤ μ) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = 2 * μ ^ 2) :
    L.stopLossExpectation X d ≤ μ - d / 2
```

`#print axioms` on every theorem reports only `propext`, `Classical.choice`,
`Quot.sound` — no `sorry`, no custom axioms.

## Build

```bash
lake update          # Mathlib v4.36.0
lake exe cache get   # prebuilt oleans (~7 GB)
lake build
```

## Run the experiments

```bash
python3 experiments/bernoulli_check.py
```
No third-party dependencies; exact rational arithmetic throughout.

## How to contribute

Open an issue with the `research-question` or `counterexample` label. Claims must
carry a status label from `LITERATURE.md`; unproved statements stay out of
`Depunc/`.

## Licence

Apache-2.0 (code). Documentation CC BY 4.0.
