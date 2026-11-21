/-
# Track A: sharp stop-loss bounds under mean and variance constraints

The Schmitter problem asks for the extremal ruin probability over claim-size
distributions with prescribed moments.  The mechanism that makes it hard — and
tractable in special cases — is that ruin probabilities are ordered by *stop-loss
order*, so the question reduces to extremal stop-loss transforms
`E[(X - d)⁺]` under moment constraints.

This file proves one sharp case exactly: for non-negative claims with

* `E[X] = μ`  and  `Var(X) = μ²`  (coefficient of variation 1),

the stop-loss transform is bounded by

  `E[(X - d)⁺] ≤ μ - d/2`   for every `0 ≤ d ≤ μ`,

with equality for the two-point law `{0, 2μ}` (mass `1/2` each).  The bound is
proved by a *dual certificate*: the quadratic

  `q(x) = (1 - d/μ) x + d x² / (4 μ²)`

majorises `(x - d)⁺` on `[0, ∞)`, and the excess over `(x - d)⁺` is exactly the
square `d (x - 2μ)² / (4 μ²)` above the kink.  That square is why the constant is
sharp and why equality forces support inside `{0, 2μ}`.

Everything is stated for finite laws in `ℚ`, so the development is kernel-checked
with exact arithmetic and no measure theory.  The measure-theoretic extension is
a one-line monotonicity argument on top of `stopLoss_majorant`.
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

open Finset

/-- A finite law: non-negative weights.  Weights are not required to sum to one;
only the moment constraints are used. -/
structure FinLaw (ι : Type*) [Fintype ι] where
  mass : ι → ℚ
  nonneg : ∀ i, 0 ≤ mass i

variable {ι : Type*} [Fintype ι]

namespace FinLaw

/-- Expected value of `X` under the law. -/
def mean (L : FinLaw ι) (X : ι → ℚ) : ℚ := ∑ i, L.mass i * X i

/-- Second moment of `X` under the law. -/
def secondMoment (L : FinLaw ι) (X : ι → ℚ) : ℚ := ∑ i, L.mass i * (X i) ^ 2

/-- Expected stop-loss payment `E[(X - d)⁺]`. -/
def stopLossExpectation (L : FinLaw ι) (X : ι → ℚ) (d : ℚ) : ℚ :=
  ∑ i, L.mass i * max (X i - d) 0

/-- Linear pulling-out lemma: a quadratic combination of `X` splits into the mean
and the second moment. -/
lemma sum_quadratic (L : FinLaw ι) (X : ι → ℚ) (a b : ℚ) :
    (∑ i, L.mass i * (a * X i + b * (X i) ^ 2))
      = a * L.mean X + b * L.secondMoment X := by
  simp only [mean, secondMoment]
  have h : ∀ i, L.mass i * (a * X i + b * (X i) ^ 2)
      = a * (L.mass i * X i) + b * (L.mass i * (X i) ^ 2) := by
    intro i; ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]

end FinLaw

/-- **The dual certificate, pointwise.**  For `0 < μ`, `0 ≤ d ≤ μ` and `x ≥ 0`,

  `4 μ² (x - d)⁺ ≤ 4 μ² x - 4 μ d x + d x²`.

The right-hand side is `4 μ²` times the quadratic majorant; the identity
`4 μ² x - 4 μ d x + d x² - 4 μ² (x - d) = d (x - 2μ)²` above the kink is the
reason the constant is sharp. -/
theorem stopLoss_majorant {μ d x : ℚ} (hμ : 0 < μ) (hd : 0 ≤ d) (hdμ : d ≤ μ)
    (hx : 0 ≤ x) :
    4 * μ ^ 2 * max (x - d) 0 ≤ 4 * μ ^ 2 * x - 4 * μ * d * x + d * x ^ 2 := by
  by_cases h : x ≤ d
  · -- below the kink the payoff vanishes; the majorant is non-negative
    have hz : max (x - d) 0 = 0 := max_eq_right (by linarith)
    rw [hz]
    have h1 : 0 ≤ 4 * μ * (μ - d) := by
      have : 0 ≤ μ - d := by linarith
      positivity
    have h2 : 0 ≤ d * x := mul_nonneg hd hx
    nlinarith [h1, h2, hx]
  · -- above the kink the excess is a perfect square
    have hz : max (x - d) 0 = x - d := max_eq_left (by linarith)
    rw [hz]
    have hsq : 0 ≤ d * (x - 2 * μ) ^ 2 := by positivity
    nlinarith [hsq]

/-- **Sharp stop-loss bound.**  For any finite law on `[0, ∞)` with `E[X] = μ` and
`E[X²] = 2μ²` (i.e. `Var X = μ²`), and any `0 ≤ d ≤ μ`:

  `E[(X - d)⁺] ≤ μ - d/2`. -/
theorem stopLoss_bound (L : FinLaw ι) (X : ι → ℚ) {μ d : ℚ} (hμ : 0 < μ)
    (hd : 0 ≤ d) (hdμ : d ≤ μ) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = 2 * μ ^ 2) :
    L.stopLossExpectation X d ≤ μ - d / 2 := by
  have h4 : 0 < 4 * μ ^ 2 := by positivity
  -- multiply the pointwise inequality by the mass and sum
  have hsum : 4 * μ ^ 2 * L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (4 * μ ^ 2 * X i - 4 * μ * d * X i + d * (X i) ^ 2) := by
    rw [FinLaw.stopLossExpectation, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have hpt := stopLoss_majorant hμ hd hdμ (hX i)
    have hm : (0 : ℚ) ≤ L.mass i := L.nonneg i
    have h1 : L.mass i * (4 * μ ^ 2 * max (X i - d) 0)
        ≤ L.mass i * (4 * μ ^ 2 * X i - 4 * μ * d * X i + d * (X i) ^ 2) :=
      mul_le_mul_of_nonneg_left hpt hm
    nlinarith [h1]
  -- evaluate the right-hand side with the moment constraints
  have hrhs : (∑ i, L.mass i * (4 * μ ^ 2 * X i - 4 * μ * d * X i + d * (X i) ^ 2))
      = (4 * μ ^ 2 - 4 * μ * d) * μ + d * (2 * μ ^ 2) := by
    have hsplit : ∀ i, L.mass i * (4 * μ ^ 2 * X i - 4 * μ * d * X i + d * (X i) ^ 2)
        = L.mass i * ((4 * μ ^ 2 - 4 * μ * d) * X i + d * (X i) ^ 2) := by
      intro i; ring
    simp only [hsplit]
    rw [FinLaw.sum_quadratic, hmean, hsecond]
  rw [hrhs] at hsum
  have hid : (4 * μ ^ 2 - 4 * μ * d) * μ + d * (2 * μ ^ 2) = 4 * μ ^ 2 * (μ - d / 2) := by
    ring
  have hle : 4 * μ ^ 2 * L.stopLossExpectation X d ≤ 4 * μ ^ 2 * (μ - d / 2) := by
    linarith [hsum, hid]
  exact le_of_mul_le_mul_left hle h4

/-- Mass vector of the law with `1/2` on each of the two atoms. -/
def twoPointMass (_μ : ℚ) : Bool → ℚ := fun _ => 1 / 2

/-- Claim vector of the law `{0, 2μ}`: `false ↦ 0`, `true ↦ 2μ`. -/
def twoPointClaim (μ : ℚ) : Bool → ℚ := fun b => if b then 2 * μ else 0

/-- The two-point law `{0, 2μ}` with mass `1/2` on each atom. -/
def twoPointLaw (μ : ℚ) : FinLaw Bool :=
  ⟨twoPointMass μ, by intro i; simp [twoPointMass]⟩

/-- **Sharpness.**  The two-point law `{0, 2μ}` has mean `μ`, second moment `2μ²`,
and stop-loss expectation exactly `μ - d/2`. -/
theorem twoPoint_attains {μ d : ℚ} (_hμ : 0 ≤ μ) (hd : 0 ≤ d) (hd2 : d ≤ 2 * μ) :
    FinLaw.mean (twoPointLaw μ) (twoPointClaim μ) = μ
    ∧ FinLaw.secondMoment (twoPointLaw μ) (twoPointClaim μ) = 2 * μ ^ 2
    ∧ FinLaw.stopLossExpectation (twoPointLaw μ) (twoPointClaim μ) d = μ - d / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FinLaw.mean, twoPointLaw, twoPointMass, twoPointClaim]
  · simp [FinLaw.secondMoment, twoPointLaw, twoPointMass, twoPointClaim]
    ring
  · simp only [FinLaw.stopLossExpectation, twoPointLaw, twoPointMass, twoPointClaim,
      Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
    rw [max_eq_right (by linarith : (0 : ℚ) - d ≤ 0), max_eq_left (by linarith : (0 : ℚ) ≤ 2 * μ - d)]
    ring

-- Axiom audit: only the three standard axioms must appear.
#print axioms Research.stopLoss_majorant
#print axioms Research.stopLoss_bound
#print axioms Research.twoPoint_attains

end Research
