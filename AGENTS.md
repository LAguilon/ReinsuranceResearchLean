# AGENTS.md — operating rules for `ReinsuranceResearchLean`

Research and formalisation agent instructions. These rules are binding on every
change to this repository.

## 1. Scope

Two tracks, one repository:

* **Track A** — distribution-free stop-loss and ruin bounds under moment
  constraints (Schmitter problem family).
* **Track B** — dependence uncertainty for risk aggregation with known marginals.

Track A currently has priority.

## 2. Three-stage certificate-first pipeline (mandatory)

Never discover a bound and write Lean tactics in the same pass. Every theorem
passes three sequential gates, in this order.

### Stage A — numerical primal/dual discovery (`experiments/*.py`)

* Discretise the support; solve the primal moment problem
  (`max E[(X-d)⁺]` under the stated moment constraints) **and** the dual
  quadratic-majorant problem
  (`min E[q(X)]` over `q(x) = a + bx + cx²` with `q ≥ (x-d)⁺` on the support).
* Report: extremal atoms, weights, dual coefficients `(a, b, c)`, and the
  parameter boundaries between regimes.
* Report the numerical duality gap for every test configuration. A configuration
  with a non-zero gap is not understood yet; do not carry it into Stage B.
* State the arithmetic used. Float64 results are evidence, not proof; exact
  rationals are required for anything quoted as a constant.

### Stage B — division-free algebraic certificate (`research/*.md`)

* Derive the closed-form `q` on paper; clear denominators so the core inequality
  is a polynomial identity over `ℝ`.
* Factor the slack `q(x) - (x-d)⁺` into sums of squares and boundary terms such
  as `x ≥ 0`, `M - x ≥ 0`, so non-negativity is syntactically transparent.
* Record the regime partition explicitly, including which support points are
  active in each regime.

### Stage C — minimal-Mathlib Lean formalisation (`Research/*.lean`)

* Translate the certificate mechanically: `nlinarith`, `positivity`, `ring`.
* No new imports beyond what the existing files use unless justified in the PR
  description.

## 3. Epistemic status gate

Every theorem statement in `research/*.md` and `README.md` carries exactly one
tag:

| Tag | Meaning |
|---|---|
| `PROVED` | Novel result, kernel-checked |
| `REPRODUCED` | Known in the literature, kernel-checked here |
| `PARTIAL` | Kernel-checked only on a restricted parameter regime |
| `CONJECTURED` | Numerical or analytic evidence only |

Check `LITERATURE.md` before tagging. Never present a classical moment bound as
novel. When a theorem is classical, cite the original authors by name and DOI.

## 4. Hypothesis freeze

Once a theorem's parameter domain is stated (e.g. `0 ≤ d ≤ M`,
`0 < μ < M`, `0 ≤ σ² ≤ μ(M-μ)`), convenience assumptions may not be added to
make a tactic succeed. If the theorem splits into regimes, prove each regime
explicitly and state the split in the theorem name.

## 5. Axiom and build discipline

* Zero `sorry`, `admit`, or custom `axiom`.
* Every main theorem is followed by `#print axioms <name>`, and the output must
  be exactly `propext`, `Classical.choice`, `Quot.sound`.
* CI enforces a zero-`sorry`/`admit`/`axiom` grep; a red build blocks publication.
* Keep `lake build` fast: finite sums, `Finset`, `ℚ` or `ℝ`. Do not import
  continuous-time stochastic processes or Bochner integration for results that
  are finite-dimensional.

## 6. Track A roadmap (order is binding)

1. **Issue #4** — bounded claims `X ∈ [0, M]` with known `(μ, σ²)`; regime
   partition and sharp bounds. *Current priority.*
2. **Randomised-surplus ruin bound** — Albrecher–Araujo-Acuña (2021), connecting
   `StopLoss.lean` to `ψ(u)` through finite mixtures of stop-loss transforms.
3. **Issue #1** — general-`σ²` three-atom closed form on `[0, ∞)`
   (Genest–Marceau–Mesfioui 2002).
4. **Issues #2, #3** — full Cramér–Lundberg stop-loss monotonicity; LP duality for
   the transportation polytope.

## 7. Publication workflow

* Verified results and conjectures never share a file: conjectures stay in
  `research/` with a `CONJECTURED` tag, proofs live in `Research/`.
* Commit after each gate with a message naming the stage (`Stage A`, `Stage B`,
  `Stage C`) and the issue number.
* Push only when `lake build` is green and the zero-`sorry` gate passes.
* Scan for credentials before every push; this repository is public.
* Never publish third-party PDFs or licensed datasets; cite DOIs instead.

## 8. Repository conventions

* Package name `Research`; root module `Research.lean` imports each file.
* `FinLaw` is the finite-law structure in `Research/StopLoss.lean`; reuse it
  rather than introducing parallel probability conventions.
* Rationals for exact statements, reals only where the analysis requires them.
* Experiments are dependency-free Python 3 with `from fractions import Fraction`
  where exactness matters.
