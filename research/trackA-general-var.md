# General-σ² unbounded stop-loss bound on `[0, ∞)` (Track A, Issue #1)

Status: **`REPRODUCED`** — kernel-checked in `Research/StopLoss/GeneralVar.lean`.
Date: 2026-11-21.

## 1. Problem

For `X ≥ 0` with `E[X] = μ` and `Var X = σ²` (no upper bound), bound
`E[(X-d)⁺]` for a retention `d ≥ 0`.

## 2. Result

With `A = μ - d`, `B = σ² > 0`, `t = A + √(A²+B)` and

  `f A B s = (s²A + sB)/(s² + B) = A + B(s-A)/(s²+B)`,

  `sup E[(X-d)⁺] = f A B (min t μ)`.

Two regimes, both inherited from the bounded development:

| Regime | Condition | Extremal atoms | Value |
|---|---|---|---|
| interior | `t ≤ μ` | `{d-r, d+r}`, `r = √(A²+B)` | `(A+r)/2 = f A B t` |
| `a = 0` | `μ < t` | `{0, b₀}`, `b₀ = (μ²+B)/μ` | `f A B μ = μ(1 - d/b₀)` |

The `b = M` branch of the bounded problem disappears: with no upper bound, `b` is
never pinned to a ceiling.

## 3. Certificates

Identical to the bounded case (perfect square for the interior regime, boundary
form `d(x-b₀)²/b₀²` for `a = 0`), and both majorise on all of `[0, ∞)`, so the
bounds hold for every law with the stated moments, not only two-atom laws.

## 4. Numerical check (Stage A)

`experiments/general_var_stoploss_check.py`: enumerates three-atom laws on a
truncated support `[0, M]` with a constant grid step, for `M = 5μ` and `20μ`.
The bounded supremum approaches the formula from below and is monotone in `M`
(truncation gate PASS), as it must since `[0, M] ⊂ [0, ∞)`.

## 5. Lean

`Research/StopLoss/GeneralVar.lean`: `bound_unbounded_interior`,
`bound_unbounded_atom_zero`, `stopLoss_bound_unbounded`. Axiom footprint:
`propext`, `Classical.choice`, `Quot.sound`.

## 6. What is not claimed

Novelty. Genest–Marceau–Mesfioui (2002) and the moment-problem literature cover
mean/variance stop-loss bounds; Hürlimann (1998) remains unverified in
`LITERATURE.md`. This is a formalisation, not a new theorem.
