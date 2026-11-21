# PROJECT_CLOSE — ReinsuranceResearchLean

## Time log

| Phase | timestamp (epoch) | wall clock |
|---|---|---|
| start (T0) | 1795261710 | 2026-11-21 12:48:30 +01:00 |
| Phase 0 done | 1795262151 | corrections applied |
| Phase 1 done | 1795262151 | LEDGER.md committed |
| Phase 2 fallback | 1795262151 | measure-theoretic T1 not completed |
| Phase 3 | 1795262151 | this file |

Hard stop: 2 h from T0. Phase 3 began at T+~25 min, well inside the box.

## Final session (13:36–13:5x)

`integral_stopLoss_le` completed for `MemLp X 2 P` using `integral_mono_of_nonneg`
(0 ≤ᵐ lhs, Integrable rhs, lhs ≤ᵐ rhs) and `MemLp.integrable_sq`. Three tactic
strategies were needed only for plumbing: `Integrable.sup` (abandoned — wrong
structure), `max_eq_add_abs` (does not exist in this revision), and the final route.
Build cost rose from 3 140 to 7 224 jobs because the measure module is now in the
default target. That cost is recorded, not hidden.

## Final SHA

c941a8137123b432358b1081f3eb69d32f015fca — see the commit that adds this file.

## Claims and tags

| Claim | Tag | Evidence |
|---|---|---|
| Two-point dependence-uncertainty results (feasible interval, convex-order monotonicity) | REPRODUCED | `Research/Bernoulli.lean`, axioms audited |
| Bounded `[0,M]` unified stop-loss bound | REPRODUCED | `Research/StopLoss/BoundedUnified.lean` |
| Unbounded `[0,∞)` general-`σ²` bound | REPRODUCED | `Research/StopLoss/GeneralVar.lean` |
| Two-atom extremal structure (not three) | REPRODUCED | exact attainment table, Issue #1 |
| Envelope bound on ruin probability `ψ_F ≤ ψ_G` | PARTIAL, non-sharp | Stage A: 265 pairs, 0 violations; exact `G` only approximated |
| `ψ(u) = (λ/c)E[(X_I−u)⁺]` | **RETRACTED** | false in general; numbers in Issue #2 |
| Measure-theoretic stop-loss bound | REPRODUCED | `Research/Measure/StopLossMeasure.lean`, `integral_stopLoss_le` for `MemLp X 2 P`; build 7 224 jobs; attained by `{d−r, d+r}` (negative atom) |
| Any novelty | NOT CLAIMED | `LEDGER.md` |

## LEDGER summary

11 works cite Kaas (1991) per OpenAlex, including *Approximations of Ruin Probability
by Di-Atomic or Di-Exponential Claims* (1992) and *Extremal Moment Methods and
Stochastic Orders* (2008) — titles only, unread. 2 works cite Albrecher–Araujo-Acuña
(2021). arXiv returns nothing for the actuarial/Lean queries. Mathlib has no
`stopLoss`, no Scarf, no Cantelli inequality; `posPart` exists only for `Lp`/`AEEqFun`.

## Open questions for whoever continues

1. Issue #2: formalise the stop-loss → ruin order chain (PK series monotone in
   stochastic order of integrated tails). Stage A passed; Stage C not started.
2. Issue #3: LP duality for the transportation polytope (needed for `n ≥ 3`
   dependence uncertainty).
3. Schmitter maximisation for deterministic initial surplus — untouched.
4. ~~Measure-theoretic `integral_stopLoss_le`~~ — **done** in the final session via
   `integral_mono_of_nonneg` + `MemLp.integrable_sq`.
5. The sharp value of `sup_F ψ_F` and the looseness of `ψ_G` — UNKNOWN.

## How the errors were caught

Four defects were found and corrected, none by the kernel:

1. **Phantom regime** (`sup = μ−d`): caught by an external reviewer's instruction to
   test the claim; `(x−d)⁺ ≥ x−d` makes `μ−d` a lower bound. Fixed in PR #7.
2. **`s := t` instead of `s := r`**: caught by a failing `hsq` obligation during
   assembly. Fixed by the branch decomposition (PR #12).
3. **"every law" prose** over a finite-support statement: caught by the audit brief
   §7.2. Fixed in `5ff4878`.
4. **False ruin identity**: caught by the reviewer; confirmed numerically (the
   exponential table shows `ρF̄_I < ψ` for `u > 0`, and the renewal equation
   reproduces `ψ(1) = 0.303265330`). Retracted on Issue #2.

The kernel verified all 44 proofs; it verified none of these four sentences.
