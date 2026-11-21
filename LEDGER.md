# LEDGER — search record (2026-11-21)

Purpose: every claim about prior art in this repository must point at a row here.
Allowed phrasing: **"no existing formalisation was found by the searches listed in
LEDGER.md (limited search; absence of evidence is not evidence of absence)"**.
The words *novel*, *first* and *new result* are not used in this repository.

## Searches performed

| Query | Tool | Result | Status |
|---|---|---|---|
| works citing Kaas 1991 (`10.2143/ast.21.1.2005406`) | OpenAlex `cites:W2463256075` | 11 citing works, e.g. *Approximations of Ruin Probability by Di-Atomic or Di-Exponential Claims* (1992); *Extremal Moment Methods and Stochastic Orders* (2008) | UNREAD (titles only) |
| works citing Albrecher–Araujo-Acuña 2021 (`10.1007/s11009-021-09910-5`) | OpenAlex `cites:W3213906102` | 2 citing works: *Limit equations of adaptive Erlangization…* (2023); *Duration-dependent stochastic fluid processes…* (2023) | UNREAD (titles only) |
| `all:Schmitter` | arXiv API | 0 entries | NOT-FOUND |
| `all:stop-loss variance bound` | arXiv API | 0 entries | NOT-FOUND |
| `all:Lean actuarial formalization` | arXiv API | 0 entries | NOT-FOUND |
| `Schmitter problem ruin` | Crossref | 3 unrelated items (gambler's ruin, Parisian ruin, "A Ruin Problem") | NOT-FOUND (no Schmitter) |
| `formalisation actuarial Lean` | Crossref | 3 items, none actuarial-Lean | NOT-FOUND |
| `stop-loss bound mean variance` | Crossref | query failed (HTTP error), retried once | NOT-FOUND (failed query) |
| Bowers (1969) | not verified | likely classical source of `E[(X−d)⁺] ≤ (μ−d+√((μ−d)²+σ²))/2`; also Scarf, Lo | **UNREAD** — cited from memory of the Schmitter literature, not opened; no statement is made about its contents |


## Mathlib grep (pinned `fc4f59e5…`, v4.36.0)

| Pattern | Result | Status |
|---|---|---|
| `stopLoss`, `stop_loss` | no hits | NOT-FOUND |
| `Scarf` | no hits | NOT-FOUND |
| `Cantelli` | only Borel–Cantelli (`Probability/Martingale/BorelCantelli.lean`); no Cantelli's inequality | NOT-FOUND |
| `positivePart` | `posPart` exists for `Lp`, `AEEqFun`, `SimpleFunc` only — not for arbitrary `Ω → ℝ` | PARTIAL |
| `MemLp` + `max (X - d) 0` bounds | no hits in `Probability/Moments.lean` | NOT-FOUND |
| `integral_mono` | exists (IntervalIntegral variants confirmed; general Bochner variant present) | FOUND |

## Caveat on the arXiv zero hits

arXiv returned **0 entries** for all three queries. This is **weak evidence**, not
absence: the arXiv API is keyword-based over titles/abstracts, actuarial science is
under-represented there, and Lean formalisation of insurance mathematics is
essentially absent. Zero hits on arXiv say nothing about the actuarial literature,
which lives in ASTIN Bulletin, IME, SAJ and SSRN. The Crossref and OpenAlex rows are
the load-bearing ones.

## What this licenses

* "No existing Lean/Mathlib formalisation of moment-constrained stop-loss bounds was
  found by these searches." — supported by the grep table.
* "The two-atom extremal structure is consistent with the literature on di-atomic
  approximations (1992 paper surfaced above)." — **title only**, not read.
* Nothing about what any paper *proves*. Every citation in `LITERATURE.md` remains
  metadata-verified only.
