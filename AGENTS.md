# AGENTS.md — operating rules for `ReinsuranceResearchLean`

Research and formalisation agent instructions. These rules are binding on every
change to this repository.

## 0. Accountability (overrides convenience)

Accuracy and intellectual honesty outrank speed and theorem count. Any claim in
this repository — including prior agent output, documentation, issue text and
theorem statements — may be audited, challenged and corrected. When a claim is
broader than what is proved, correct it in place, downgrade its tag
(`PROVED` → `PARTIAL`/`CONJECTURED`) and state the mathematical reason. Never
silently delete an error; record it in the commit message and, if it was public,
in the issue thread.

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
  description. The library uses a narrow import set, not `import Mathlib`; a
  broad import is a build-time regression (18 256 → 2 080 jobs) and must be
  rejected in review.
* Every main theorem ships with a **non-vacuity witness**: an instantiation at
  concrete rational data, checked in `Research/Verify.lean`, proving the
  hypotheses are simultaneously satisfiable.

### Adversarial falsification (gate before any `PROVED`/`REPRODUCED` tag)

Before tagging, try to break the formula:

* boundary limits `d → 0`, `d → μ`, `d → M`, `σ² → 0`, `σ² → μ(M-μ)`;
* degenerate two-point laws and atoms sitting exactly on `d`, `0`, `M`;
* randomised search over admissible `(μ, σ², d)` with the dual certificate
  re-checked by dense sampling;
* an explicit numerical duality gap is a failed certificate: report it, do not
  average it away.

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

**Public errata rule.** An error discovered after publication is corrected in
place with a dated note in the file, a commit message that says what was wrong,
and — when the claim was stated in an issue or release — a correcting comment
there. A correction is never a silent edit.

## 4. Hypothesis freeze

Once a theorem's parameter domain is stated (e.g. `0 ≤ d ≤ M`,
`0 < μ < M`, `0 ≤ σ² ≤ μ(M-μ)`), convenience assumptions may not be added to
make a tactic succeed. If the theorem splits into regimes, prove each regime
explicitly and state the split in the theorem name.

## 5. Axiom and build discipline

* Zero `sorry`, `admit`, `native_decide`, or custom `axiom` (`native_decide`
  reaches `Lean.trustCompiler` and is treated as an escape hatch).
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
* Push only when `lake build` is green, `Research/Verify.lean` prints the exact
  three-axiom footprint for every theorem, and the zero-`sorry` gate passes.
* Never push unverified `.lean` changes to `main`: work on a feature branch
  (`fix/*`, `feat/*`), verify locally, then merge.
* Use `Closes #<n>` only when **every** regime of that issue is kernel-checked;
  otherwise `Refs #<n>`.
* Scan for credentials before every push; this repository is public.
* Never publish third-party PDFs or licensed datasets; cite DOIs instead.

## 8. Repository conventions

* Package name `Research`; root module `Research.lean` imports each file.
* `FinLaw` is the finite-law structure in `Research/StopLoss.lean`; reuse it
  rather than introducing parallel probability conventions.
* Rationals for exact statements, reals only where the analysis requires them.
* Experiments are dependency-free Python 3 with `from fractions import Fraction`
  where exactness matters.
