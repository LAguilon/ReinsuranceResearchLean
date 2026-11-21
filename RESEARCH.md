# Research note — dependence uncertainty for two-point risks, kernel-checked

Status: **`REPRODUCED`** (classical result, independently formalised). Not claimed
as new. Stage 1 pilot of the reinsurance research programme, Track B.
Date: 2026-11-21. Lean: 4.36.0 + Mathlib (`v4.36.0`).

## 1. The mathematical problem

Two risks `X`, `Y` with known Bernoulli marginals `P(X=1)=p`, `P(Y=1)=q`. The
joint law is unknown; only the marginals are known. What is the largest and
smallest value of `E[φ(X+Y)]` for a convex penalty `φ`, over all couplings?

## 2. Relevance to insurance

This is the smallest instance of the capital-modelling question every reinsurer
faces: aggregate loss depends on the *dependence* between lines, not only on the
marginal loss distributions. Bounds that hold for *every* admissible dependence
structure are the only numbers that survive model risk. In treaty design the
convex penalties are stop-loss covers `(x-d)⁺`, so the two-point case already
answers a real question: how much can a stop-loss layer cost change when the
dependence between two lines is unknown?

## 3. What was previously known

Upper bounds for convex functionals of aggregates with fixed marginals are
classical: comonotone coupling maximises convex order (Embrechts–Puccetti 2006;
Embrechts–Puccetti–Rüschendorf 2013), and the general finite-`n` problem is solved
exactly only in special families, with asymptotic results under complete/joint
mixability (Puccetti–Wang–Wang 2013; Wang–Wang 2016). See `LITERATURE.md`.

## 4. What was investigated here

* the geometry of the feasible set of couplings — a segment here, a transportation
  polytope in general;
* whether the extremal couplings can be identified without a solver, i.e. whether
  the optimisation collapses to the endpoints of that segment;
* a machine-checked version of the resulting theorem, with the convexity
  hypothesis reduced to a lattice second difference;
* the three-point case numerically, to see where the segment picture breaks.

## 5. What was found

1. **Feasible set is an interval.** For marginals `p, q`, the couplings are exactly
   the parameters `t = P(X=1,Y=1)` with
   `max 0 (p+q-1) ≤ t ≤ min p q`. Comonotone (`t = min p q`) and
   countermonotone (`t = max 0 (p+q-1)`) are the endpoints; the set is convex.
2. **Affine collapse.** `E[φ(X+Y)] = φ(0)(1-p-q) + φ(1)(p+q) + t·Δ²φ`, where
   `Δ²φ = φ(2) - 2φ(1) + φ(0)`. So the optimisation over dependence is affine in
   one variable: the extremum is at an endpoint, and the sign of `Δ²φ` decides
   which one.
3. **Kernel-checked consequence.** For every `φ` with `Δ²φ ≥ 0` — which includes
   every stop-loss `(x-d)⁺`, verified as `stopLoss_convex` — the comonotone
   coupling is the maximum and the countermonotone the minimum. Axiom audit:
   only `propext`, `Classical.choice`, `Quot.sound`.
4. **Where the picture breaks.** For uniform 3-point marginals the feasible set is
   a 4-dimensional polytope. Numerically (`experiments/bernoulli_check.py`,
   grid step 1/12), `ES_α(X+Y)` ranges from `2` to `10/3` at `α = 1/2` and from
   `2` to `4` at `α = 3/4`; the maximum is comonotone as theory predicts, and the
   minimum is attained by the *reverse* coupling, under which the sum is constant
   (`Y = 2 - X`, so `X+Y = 2`). Constant-sum couplings are exactly the
   joint-mixability phenomenon, and they have no two-point analogue: with two
   atoms the sum cannot be constant unless `p` or `q` is degenerate.
5. **No new theorem is claimed.** The audit does not support a novelty claim, and
   the environment has no keyword search, so novelty cannot be certified here.

## 6. Formulation

Let `p, q, t ∈ ℚ` and define the four cell masses

| | Y = 0 | Y = 1 |
|---|---|---|
| **X = 0** | `1-p-q+t` | `q-t` |
| **X = 1** | `p-t` | `t` |

`Coupling p q t` is the predicate that all four are non-negative and sum to one,
equivalently `0 ≤ t`, `t ≤ p`, `t ≤ q`, `p+q-t ≤ 1`.

**Theorem** (`Coupling.expCost_le_comonotone`). For `0 ≤ p,q ≤ 1`, `t` feasible,
and `φ : ℚ → ℚ` with `φ(2) - 2φ(1) + φ(0) ≥ 0`:
`E_t[φ(X+Y)] ≤ E_{min p q}[φ(X+Y)]`.

**Theorem** (`Coupling.countermonotone_le_expCost`). Under the same convexity
hypothesis and any feasible `t`: `E_{max 0 (p+q-1)}[φ(X+Y)] ≤ E_t[φ(X+Y)]`.

## 7. Assumptions

* Bernoulli marginals (two atoms). The general case is not covered.
* `φ` evaluated only on `{0,1,2}`, so "convexity" is the lattice condition
  `Δ²φ ≥ 0`; no continuity or measurability is needed.
* Rationals `ℚ` rather than `ℝ` — exact arithmetic, no rounding, and the
  statements transfer to `ℝ` by the same proofs.
* `0 ≤ p, q ≤ 1` is required only for the two endpoint-feasibility lemmas.

## 8. Proof strategy

`expCost_affine` rewrites the objective as an affine function of `t` (`ring`), so
monotonicity in `t` is `mul_le_mul_of_nonneg_right` applied to `Δ²φ ≥ 0`
(`expCost_mono`). Feasibility of the endpoints is `max_le`/`le_min` plus
`linarith`. Convexity of the stop-loss transform on the lattice is a four-way
sign case split discharged by `split_ifs <;> linarith`.

## 9. Lean implementation

* `Depunc/Bernoulli.lean` — definitions, `coupling_iff`, `convex`, `expCost`,
  `expCost_affine`, `expCost_mono`, both extremal theorems, `stopLoss`,
  `stopLoss_convex`, axiom audit.
* Build: `lake build` (Mathlib `v4.36.0` required).
* Experiments: `experiments/bernoulli_check.py` (pure Python, no dependencies).

## 10. What remains unresolved

* Finite-`n` sharp **lower** bounds for ES with fixed marginals: the hard half.
  `OPEN_CANDIDATE` in this audit, not certified open.
* Couplings with partial dependence information (e.g. a known copula family
  bound) — the affine collapse is lost, and the objective becomes piecewise
  linear over a polytope; requires an LP-duality development that Mathlib does
  not currently provide.
* General marginals, from which the two-point case follows as a corollary, and
  which would connect to the Schmitter problem via stop-loss order (Track A).
* Optimal reinsurance with dependence uncertainty under a budget constraint
  (Fadina–Hu–Liu–Xia 2025): the tractable structure is an infinite-dimensional
  optimisation; nothing formalised.
