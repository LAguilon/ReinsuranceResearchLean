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

Track A had priority. **The repository is a closed experiment (2026-11-21)** — see
§10. Do not start new research here without an explicit written request.

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
* A quadratic dual need not exist. If the extremal majorant is piecewise linear or
  the slack is a boundary term, certify with that object and say so; a non-zero
  quadratic gap is not by itself a failure of the bound.
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
  description. The **core tier** uses a narrow import set, not `import Mathlib`; a
  broad import there is a build-time regression (18 256 → 3 140 jobs) and must be
  rejected in review. The **measure tier** (`Research/Measure/`) may import
  `Mathlib.MeasureTheory`; it is isolated in its own directory and raises the
  default target from 3 140 to 7 224 jobs, which is recorded in the README rather
  than hidden.
* Every main theorem ships with a **non-vacuity witness**: an instantiation at
  concrete data (rational where the tier allows it), checked in
  `Research/Verify.lean`, proving the hypotheses are simultaneously satisfiable.
  Where the statement is measure-theoretic and no witness is written, say so.

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
| `PROVED` | Novel result, kernel-checked, with a `LEDGER.md` row listing the searches performed |
| `REPRODUCED` | Known in the literature, kernel-checked here |
| `PARTIAL` | Kernel-checked only on a restricted parameter regime |
| `CONJECTURED` | Numerical or analytic evidence only |
| `STATUS_UNCERTAIN` | Literature status unknown; the statement may or may not be known |

Check `LITERATURE.md` before tagging. Never present a classical moment bound as
novel. When a theorem is classical, cite the original authors by name and DOI.

**Prior-art rule.** Every claim about what exists in the literature points to a row
in `LEDGER.md`. Allowed phrasing: "no existing formalisation was found by the
searches listed in `LEDGER.md` (limited search; absence of evidence is not evidence
of absence)". The words *novel*, *first*, *discovery*, *breakthrough* and *solves*
are not used in public text.

**Fidelity table rule.** Every public theorem ships with three columns: the formal
statement (Lean signature), the prose claim it licenses, and what it does **not**
claim. The third column is mandatory and must be non-empty.

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
* Every main theorem is registered in `Research/Verify.lean` with
  `#print axioms <name>` (not inline in the source), and the output must be
  exactly `propext`, `Classical.choice`, `Quot.sound`. The CI floor must equal the
  number of registered declarations (currently 46).
* CI enforces a zero-`sorry`/`admit`/`axiom` grep; a red build blocks publication.
* Keep `lake build` fast: finite sums, `Finset`, `ℚ` or `ℝ`. Do not import
  continuous-time stochastic processes, and do not import Bochner integration for
  finite-dimensional results. The single sanctioned exception is
  `Research/Measure/`, where the measure-theoretic statement is the point.

## 6. Track A roadmap (historical order; the repository is closed)

1. ~~**Issue #4** — bounded claims `X ∈ [0, M]`.~~ **Done** (PRs #11, #12): unified
   `stopLoss_bound_bounded`, issue closed.
2. **Randomised-surplus ruin bound** — Albrecher–Araujo–Acuña (2021). **Not started.**
   Blocked on a modelling decision (pin the third moment via a family, or carry a
   three-moment hypothesis); see Issue #2.
3. ~~**Issue #1** — general-`σ²` closed form on `[0, ∞)`.~~ **Done** (PR #13):
   `stopLoss_bound_unbounded`; the extremal law is **two**-atom, not three.
4. **Issues #2, #3** — Cramér–Lundberg stop-loss monotonicity; LP duality for the
   transportation polytope. **Not started.**

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
* `FinLaw` is the finite-law structure in `Research/StopLoss.lean`; `FinLawR` is
  its real-valued twin in `Research/Real/Sqrt.lean`. Reuse them rather than
  introducing parallel probability conventions. The measure tier uses
  `MeasureTheory.Measure` and does not touch either structure.
* Rationals for exact statements, reals only where the analysis requires them.
* Experiments are dependency-free Python 3 with `from fractions import Fraction`
  where exactness matters.

## 9. Self-sufficient execution and anti-stall protocol

1. **No permission loops.** Do not ask "should I proceed to Stage C?" or "which
   issue next?". Execute Stage A → Stage B → Stage C end to end and advance down
   the roadmap queue automatically. Approval is assumed for research direction,
   file layout, branches, PR merges once CI is green, and errata corrections.
2. **Three-attempt tactic cap.** If a Lean proof fails after three distinct tactic
   strategies (or exhausts a heartbeat), stop. Isolate the lemmas that do compile,
   record the exact algebraic blocker in `research/*.md`, tag the theorem
   `PARTIAL`, merge the clean progress, and move on. Do not thrash.
3. **Build-time budget.** Keep `lake build` under **7 500 jobs / 20 s** (current
   7 224 jobs / 8.3 s; the core tier alone is 3 140). `Mathlib.Analysis.Real.Sqrt`
   stays inside `Research/Real/` and `Mathlib.MeasureTheory` inside
   `Research/Measure/`, so each tier's cost is attributable.
   Split growing files into submodules (`Research/StopLoss/Interior.lean`,
   `Bounded.lean`, `GeneralVar.lean`, `Ruin.lean`) instead of accumulating one
   file of `nlinarith` calls.
4. **Dual-certificate exhaustiveness.** When pointwise majorants `qᵢ ≥ f` cover a
   partition of the parameter space, proving the partition is exhaustive proves
   exhaustiveness over *all* laws, because expectation is linear and monotone.
   Prefer this to Carathéodory machinery; the measure tier exists only for
   statements that genuinely need it. Corollary: never take a maximum over
   candidate *formulas*; the supremum is the smallest valid upper bound, so
   candidates must be certified before they are compared.
5. **Scientific accountability.** Correct any mathematical error, phantom regime
   or overstated claim immediately, in code, docs, README and GitHub issues, and
   keep the `PROVED` / `REPRODUCED` / `PARTIAL` / `CONJECTURED` /
   `STATUS_UNCERTAIN` tags exact at every merge. This applies to instructions received from outside as well: verify
   claims before adopting them.

### 9b. Amendments (2026-11-21) — per-lemma ratchet

1. **Per-lemma 3-attempt cap.** The three-strategy limit applies to one lemma, never
   to total build iterations across a multi-lemma file. Fixing three sub-lemmas
   across three builds is normal progress, not stalling.
2. **Monotonic ratchet.** Never delete a file because one lemma fails. Strip only
   the unproved theorem, commit and merge the helpers that compile, log the blocker
   on the issue, and continue.
3. **Micro-slices.** Build 1–2 lemmas (20–40 lines) at a time; do not write a
   150-line assembly before the first `lake build`.
4. **Continuous run.** Do not emit status messages mid-queue; only report when the
   queue is done or every remaining item is genuinely blocked.

### 9c. Assembly rules (2026-11-21)

1. **45-line theorem cap.** No assembly theorem over ~45 lines. Split multi-regime
   proofs into standalone branch lemmas (≤ 40 lines) plus a short dispatcher. If a
   lemma hits the cap, split it or pivot to the next milestone — do not stop.
2. **No blind `subst`.** `subst h` on `h : d = M` eliminates `M`; use `rw [h]`.
3. **Named arguments** on multi-hypothesis calls (`(hμ := …) (hd := …)`).
4. **No opaque `set` before `rw`** with external lemmas; unfold first.
5. **Explicit slope rewrite** (`field_simp; ring`) before `nlinarith` on a slope
   side condition.

## 10. Status — closed experiment (2026-11-21)

This repository is **closed**. It is a record, not an active project.

* **What is checked:** 46 declarations, zero `sorry`, zero custom `axiom`, every
  footprint exactly `propext, Classical.choice, Quot.sound`. 11 carry mathematical
  content; the rest are witnesses and algebra helpers.
* **What is classical:** all of it. Citations are metadata-verified only; no paper
  was read.
* **What is absent:** any formalised ruin probability; any solution of the
  Schmitter problem; any optimal-reinsurance theorem; any novelty claim.
* **What is known to be loose:** the stop-loss *envelope* bound on `ψ` is valid but
  non-sharp, and the sharp value of `sup_F ψ_F` is unknown.

**Resuming.** Any resumption requires a written scope: the target theorem, the
parameter domain, the status tag it is expected to reach, and the build budget it
may spend. Without that, new work does not start.
