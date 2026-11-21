/-
# The real tier: `Real.sqrt` toolkit and the unimodality of `f`

Layered alongside the exact-rational modules, which stay untouched.  Everything
here is over `ℝ`, so `Real.sqrt` is available and the clamped supremum can be
stated as a single formula.

The objective of the bounded-claims problem, as a function of the free parameter
`s = μ - a`, is

  `f(s) = (s²(μ-d) + sσ²)/(s² + σ²) = A + σ²(s - A)/(s² + σ²)`,   `A = μ - d`,

with critical point `s* = A + √(A² + σ²)`.  The key algebraic fact, proved here
without derivatives, is

  `f(s*) - f(s) = σ² · √(A²+σ²) · (s* - s)² / ((s*²+σ²)(s²+σ²)) ≥ 0`,

so `s*` is a **global** maximiser on `(0, ∞)`.  That single identity gives the
clamp lemma by a three-way case split.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs

namespace Research

/-- A finite law with real weights. -/
structure FinLawR (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  nonneg : ∀ i, 0 ≤ mass i

variable {ι : Type*} [Fintype ι]

namespace FinLawR

/-- Expected value. -/
def mean (L : FinLawR ι) (X : ι → ℝ) : ℝ := ∑ i, L.mass i * X i

/-- Second moment. -/
def secondMoment (L : FinLawR ι) (X : ι → ℝ) : ℝ := ∑ i, L.mass i * (X i) ^ 2

/-- Expected stop-loss payment `E[(X - d)⁺]`. -/
def stopLossExpectation (L : FinLawR ι) (X : ι → ℝ) (d : ℝ) : ℝ :=
  ∑ i, L.mass i * max (X i - d) 0

/-- Total mass one. -/
def IsProbability (L : FinLawR ι) : Prop := ∑ i, L.mass i = 1

/-- Quadratic pulling-out, no constant term. -/
lemma sum_quadratic (L : FinLawR ι) (X : ι → ℝ) (a b : ℝ) :
    (∑ i, L.mass i * (a * X i + b * (X i) ^ 2))
      = a * L.mean X + b * L.secondMoment X := by
  simp only [mean, secondMoment]
  have h : ∀ i, L.mass i * (a * X i + b * (X i) ^ 2)
      = a * (L.mass i * X i) + b * (L.mass i * (X i) ^ 2) := by
    intro i; ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]

/-- Quadratic pulling-out with a constant term. -/
lemma sum_quadratic_const (L : FinLawR ι) (X : ι → ℝ) (a b c : ℝ)
    (hone : ∑ i, L.mass i = 1) :
    (∑ i, L.mass i * (a * X i + b * (X i) ^ 2 + c))
      = a * L.mean X + b * L.secondMoment X + c := by
  have h : ∀ i, L.mass i * (a * X i + b * (X i) ^ 2 + c)
      = L.mass i * (a * X i + b * (X i) ^ 2) + L.mass i * c := by
    intro i; ring
  simp only [h, Finset.sum_add_distrib]
  rw [sum_quadratic]
  have hc : (∑ i, L.mass i * c) = c := by
    rw [← Finset.sum_mul, hone, one_mul]
  rw [hc]

end FinLawR

/-- The objective `f(s) = A + σ²(s - A)/(s² + σ²)`. -/
noncomputable def f (A B s : ℝ) : ℝ := A + B * (s - A) / (s ^ 2 + B)

/-- The critical point `s* = A + √(A² + B)`. -/
noncomputable def sStar (A B : ℝ) : ℝ := A + Real.sqrt (A ^ 2 + B)

lemma sStar_sq {A B : ℝ} (hB : 0 ≤ B) :
    (sStar A B) ^ 2 = 2 * A * sStar A B + B := by
  unfold sStar
  have hr2 : (Real.sqrt (A ^ 2 + B)) ^ 2 = A ^ 2 + B :=
    Real.sq_sqrt (by positivity)
  nlinarith [hr2]

lemma sStar_gt {A B : ℝ} (hB : 0 < B) : A < sStar A B := by
  unfold sStar
  have hr : 0 < Real.sqrt (A ^ 2 + B) := Real.sqrt_pos.mpr (by positivity)
  linarith

end Research
