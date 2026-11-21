/-
# Dependence uncertainty for two Bernoulli risks

Two risks `X` and `Y` with Bernoulli marginals `P(X = 1) = p`, `P(Y = 1) = q`.
Every coupling is determined by the single number `t = P(X = 1, Y = 1)`:

| X \ Y | 0        | 1   |
|-------|----------|-----|
| 0     | 1-p-q+t  | q-t |
| 1     | p-t      | t   |

The feasible set of `t` is an interval, and the expected value of any convex
penalty `φ` applied to the aggregate `X + Y` is an *affine* function of `t`.
Consequently, for convex `φ` the aggregate is largest in convex order under the
comonotone coupling (`t = min p q`) and smallest under the countermonotone
coupling (`t = max 0 (p+q-1)`).

This is the exactly solvable case of the general dependence-uncertainty
programme: in general the feasible set is a transportation polytope and the
extremal couplings are not the obvious ones; here it is a segment, so the
optimisation collapses to its endpoints.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FieldSimp

namespace Research

/-- A coupling of two Bernoulli risks with marginals `p`, `q` and
`t = P(X = 1, Y = 1)`, encoded by the three independent constraints on the
joint law (the fourth cell mass is then automatic). -/
structure Coupling (p q t : ℚ) : Prop where
  ht0 : 0 ≤ t
  htp : t ≤ p
  htq : t ≤ q
  hsum : p + q - t ≤ 1

namespace Coupling

variable {p q t : ℚ}

/-- Mass of the cell `(X, Y) = (0, 0)`. -/
def m00 (p q t : ℚ) : ℚ := 1 - p - q + t

/-- Mass of the cell `(X, Y) = (1, 0)`. -/
def m10 (p t : ℚ) : ℚ := p - t

/-- Mass of the cell `(X, Y) = (0, 1)`. -/
def m01 (q t : ℚ) : ℚ := q - t

/-- Mass of the cell `(X, Y) = (1, 1)`. -/
def m11 (t : ℚ) : ℚ := t

/-- All four cell masses are non-negative. -/
lemma cells_nonneg (h : Coupling p q t) :
    0 ≤ m00 p q t ∧ 0 ≤ m10 p t ∧ 0 ≤ m01 q t ∧ 0 ≤ m11 t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold m00; linarith [h.hsum]
  · unfold m10; linarith [h.htp]
  · unfold m01; linarith [h.htq]
  · unfold m11; exact h.ht0

/-- The four cell masses sum to one, so the joint law is a probability law. -/
lemma cells_sum (p q t : ℚ) :
    m00 p q t + m10 p t + m01 q t + m11 t = 1 := by
  unfold m00 m10 m01 m11; ring

/-- The feasible dependence parameters form an interval. -/
theorem convex {t₁ t₂ t : ℚ} (h₁ : Coupling p q t₁) (h₂ : Coupling p q t₂)
    (h₁₂ : t₁ ≤ t) (h₂₃ : t ≤ t₂) : Coupling p q t where
  ht0 := le_trans h₁.ht0 h₁₂
  htp := le_trans h₂₃ h₂.htp
  htq := le_trans h₂₃ h₂.htq
  hsum := by linarith [h₁.hsum, h₁₂]

/-- Feasibility is exactly the closed interval between the countermonotone and
comonotone parameters. -/
theorem iff (p q t : ℚ) :
    Coupling p q t ↔ max 0 (p + q - 1) ≤ t ∧ t ≤ min p q := by
  constructor
  · intro h
    exact ⟨max_le h.ht0 (by linarith [h.hsum]), le_min h.htp h.htq⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨le_trans (le_max_left 0 (p + q - 1)) hlo, ?_, ?_, ?_⟩
    · exact le_trans hhi (min_le_left p q)
    · exact le_trans hhi (min_le_right p q)
    · have : p + q - 1 ≤ max 0 (p + q - 1) := le_max_right _ _
      linarith

/-- Expected cost `E[φ(X + Y)]` under the coupling with parameter `t`. -/
def expCost (φ : ℚ → ℚ) (p q t : ℚ) : ℚ :=
  φ 0 * m00 p q t + φ 1 * (m10 p t + m01 q t) + φ 2 * m11 t

/-- The expected cost is affine in the dependence parameter. -/
lemma expCost_affine (φ : ℚ → ℚ) (p q t : ℚ) :
    expCost φ p q t
      = (φ 0 * (1 - p - q) + φ 1 * (p + q)) + t * (φ 2 - 2 * φ 1 + φ 0) := by
  unfold expCost m00 m10 m01 m11; ring

/-- **Convex order is monotone in the dependence parameter.**  If the discrete
second difference of `φ` at `0, 1, 2` is non-negative — the exact convexity
condition on the lattice `{0, 1, 2}` that the aggregate lives on — then a larger
`t` means a larger expected cost. -/
theorem expCost_mono (φ : ℚ → ℚ) (p q : ℚ) {t₁ t₂ : ℚ} (ht : t₁ ≤ t₂)
    (hconv : 0 ≤ φ 2 - 2 * φ 1 + φ 0) :
    expCost φ p q t₁ ≤ expCost φ p q t₂ := by
  rw [expCost_affine, expCost_affine]
  have h : t₁ * (φ 2 - 2 * φ 1 + φ 0) ≤ t₂ * (φ 2 - 2 * φ 1 + φ 0) :=
    mul_le_mul_of_nonneg_right ht hconv
  linarith

/-- The comonotone parameter is feasible. -/
lemma comonotone_feasible {p q : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Coupling p q (min p q) := by
  rw [iff]
  refine ⟨?_, le_rfl⟩
  apply max_le (le_min hp0 hq0)
  apply le_min <;> linarith

/-- The countermonotone parameter is feasible. -/
lemma countermonotone_feasible {p q : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Coupling p q (max 0 (p + q - 1)) := by
  rw [iff]
  refine ⟨le_rfl, max_le (le_min hp0 hq0) (le_min ?_ ?_)⟩
  · linarith
  · linarith

/-- **Main theorem (upper bound).**  For convex `φ`, the comonotone coupling
maximises the expected aggregate cost among all couplings with the given
marginals. -/
theorem expCost_le_comonotone (φ : ℚ → ℚ) {p q : ℚ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1) (hconv : 0 ≤ φ 2 - 2 * φ 1 + φ 0)
    (h : Coupling p q t) :
    expCost φ p q t ≤ expCost φ p q (min p q) :=
  expCost_mono φ p q (le_min h.htp h.htq) hconv

/-- **Main theorem (lower bound).**  For convex `φ`, the countermonotone coupling
minimises the expected aggregate cost. -/
theorem countermonotone_le_expCost (φ : ℚ → ℚ) {p q t : ℚ}
    (hconv : 0 ≤ φ 2 - 2 * φ 1 + φ 0) (h : Coupling p q t) :
    expCost φ p q (max 0 (p + q - 1)) ≤ expCost φ p q t :=
  expCost_mono φ p q (max_le h.ht0 (by linarith [h.hsum])) hconv

end Coupling

/-- Stop-loss transform `x ↦ (x - d)⁺`. -/
def stopLoss (d x : ℚ) : ℚ := if 0 ≤ x - d then x - d else 0

/-- On the lattice `{0, 1, 2}` the stop-loss transform has a non-negative second
difference for every deductible `d`, i.e. it is convex. -/
theorem stopLoss_convex (d : ℚ) :
    0 ≤ stopLoss d 2 - 2 * stopLoss d 1 + stopLoss d 0 := by
  unfold stopLoss
  split_ifs <;> linarith

end Research

/-! ## Axiom audit

The whole file must rest only on Lean's three standard axioms. -/

#print axioms Research.Coupling.iff
#print axioms Research.Coupling.expCost_mono
#print axioms Research.Coupling.expCost_le_comonotone
#print axioms Research.Coupling.countermonotone_le_expCost
#print axioms Research.stopLoss_convex
