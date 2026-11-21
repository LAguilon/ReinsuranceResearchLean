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

/-! ## Unimodality

The identities below are exact polynomial identities (proved by `ring`), not
`nlinarith` searches: the sign of the cross-multiplied difference is read off
from a factorisation around the critical point `t = s*`. -/

lemma sStar_sub_A_nonneg (A B : ℝ) : 0 ≤ sStar A B - A := by
  unfold sStar
  have := Real.sqrt_nonneg (A ^ 2 + B)
  linarith

/-- `2A ≤ s*`. -/
lemma two_mul_le_sStar {A B : ℝ} (hB : 0 ≤ B) : 2 * A ≤ sStar A B := by
  have h : A ≤ Real.sqrt (A ^ 2 + B) := by
    by_cases hA : A ≤ 0
    · linarith [Real.sqrt_nonneg (A ^ 2 + B)]
    · have hApos : 0 < A := not_le.mp hA
      have hmono : Real.sqrt (A ^ 2) ≤ Real.sqrt (A ^ 2 + B) :=
        Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq (le_of_lt hApos)] at hmono
  unfold sStar
  linarith

/-- Cross-multiplied numerator identity. -/
lemma f_diff_num (A B s1 s2 : ℝ) :
    (s2 - A) * (s1 ^ 2 + B) - (s1 - A) * (s2 ^ 2 + B)
      = (s2 - s1) * (B + A * (s1 + s2) - s1 * s2) := by ring

/-- **Increasing side.**  `f` is non-decreasing on `(0, s*]`. -/
theorem f_inc {A B s1 s2 : ℝ} (hB : 0 ≤ B) (hs1 : 0 < s1) (h12 : s1 ≤ s2)
    (h2t : s2 ≤ sStar A B) : f A B s1 ≤ f A B s2 := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · subst hB0; unfold f; simp
  have ht : (sStar A B) ^ 2 = 2 * A * sStar A B + B := sStar_sq hB
  have h2A : 2 * A ≤ sStar A B := two_mul_le_sStar hB
  have hbr : 0 ≤ B + A * (s1 + s2) - s1 * s2 := by
    have hfac : B + A * (s1 + s2) - s1 * s2
        = (B + 2 * A * (sStar A B) - (sStar A B) ^ 2)
          + ((sStar A B) - s2) * ((sStar A B) - 2 * A + s1)
          + ((sStar A B) - A) * (s2 - s1) := by ring
    have h0 : B + 2 * A * (sStar A B) - (sStar A B) ^ 2 = 0 := by nlinarith [ht]
    rw [hfac, h0]
    have h1 : 0 ≤ (sStar A B) - s2 := by linarith
    have h2 : 0 ≤ (sStar A B) - 2 * A + s1 := by linarith
    have h3 : 0 ≤ (sStar A B) - A := sStar_sub_A_nonneg A B
    have h4 : 0 ≤ s2 - s1 := by linarith
    have hm1 := mul_nonneg h1 h2
    have hm2 := mul_nonneg h3 h4
    linarith
  have hden1 : 0 < s2 ^ 2 + B := by nlinarith [sq_nonneg s2, hBpos, hs1, h12]
  have hden2 : 0 < s1 ^ 2 + B := by nlinarith [sq_nonneg s1, hBpos, hs1]
  have hkey : f A B s2 - f A B s1
      = B * ((s2 - A) * (s1 ^ 2 + B) - (s1 - A) * (s2 ^ 2 + B))
          / ((s2 ^ 2 + B) * (s1 ^ 2 + B)) := by
    unfold f
    field_simp
    ring
  have hnum : 0 ≤ B * ((s2 - A) * (s1 ^ 2 + B) - (s1 - A) * (s2 ^ 2 + B)) := by
    rw [f_diff_num]
    exact mul_nonneg hB (mul_nonneg (by linarith) hbr)
  have : 0 ≤ f A B s2 - f A B s1 := by
    rw [hkey]
    positivity
  linarith

/-- **Decreasing side.**  `f` is non-increasing on `[s*, ∞)`. -/
theorem f_dec {A B s1 s2 : ℝ} (hB : 0 ≤ B) (hs1 : 0 < s1) (ht1 : sStar A B ≤ s1)
    (h12 : s1 ≤ s2) : f A B s2 ≤ f A B s1 := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · subst hB0; unfold f; simp
  have ht : (sStar A B) ^ 2 = 2 * A * sStar A B + B := sStar_sq hB
  have h2A : 2 * A ≤ sStar A B := two_mul_le_sStar hB
  have hbr : B + A * (s1 + s2) - s1 * s2 ≤ 0 := by
    have hfac : B + A * (s1 + s2) - s1 * s2
        = (B + 2 * A * (sStar A B) - (sStar A B) ^ 2)
          - (s1 - sStar A B) * (sStar A B - 2 * A + s2)
          - ((sStar A B) - A) * (s2 - s1) := by ring
    have h0 : B + 2 * A * (sStar A B) - (sStar A B) ^ 2 = 0 := by nlinarith [ht]
    rw [hfac, h0]
    have h1 : 0 ≤ s1 - sStar A B := by linarith
    have h2 : 0 ≤ (sStar A B) - 2 * A + s2 := by linarith
    have h3 : 0 ≤ (sStar A B) - A := sStar_sub_A_nonneg A B
    have h4 : 0 ≤ s2 - s1 := by linarith
    have hm1 := mul_nonneg h1 h2
    have hm2 := mul_nonneg h3 h4
    linarith
  have hden1 : 0 < s2 ^ 2 + B := by nlinarith [sq_nonneg s2, hBpos, hs1, h12]
  have hden2 : 0 < s1 ^ 2 + B := by nlinarith [sq_nonneg s1, hBpos, hs1]
  have hkey : f A B s1 - f A B s2
      = B * ((s1 - A) * (s2 ^ 2 + B) - (s2 - A) * (s1 ^ 2 + B))
          / ((s1 ^ 2 + B) * (s2 ^ 2 + B)) := by
    unfold f
    field_simp
    ring
  have hnum : 0 ≤ B * ((s1 - A) * (s2 ^ 2 + B) - (s2 - A) * (s1 ^ 2 + B)) := by
    have hneg : (s1 - A) * (s2 ^ 2 + B) - (s2 - A) * (s1 ^ 2 + B)
        = (s1 - s2) * (B + A * (s1 + s2) - s1 * s2) := by ring
    rw [hneg]
    exact mul_nonneg hB (mul_nonneg_of_nonpos_of_nonpos (by linarith) hbr)
  have : 0 ≤ f A B s1 - f A B s2 := by
    rw [hkey]
    positivity
  linarith

/-- **Clamp lemma.**  On `[lo, hi] ⊂ (0, ∞)` the maximum of `f` is at the clamp of
`s*` into the interval. -/
theorem f_le_clamp {A B lo hi s : ℝ} (hB : 0 ≤ B) (hlo0 : 0 < lo) (hlo : lo ≤ s)
    (hhi : s ≤ hi) :
    f A B s ≤ f A B (max lo (min (sStar A B) hi)) := by
  by_cases h1 : sStar A B ≤ lo
  · have hcl : max lo (min (sStar A B) hi) = lo := by
      rw [min_eq_left (le_trans h1 (le_trans hlo hhi)), max_eq_left h1]
    rw [hcl]
    exact f_dec (s1 := lo) (s2 := s) hB hlo0 h1 hlo
  · have h1' : lo < sStar A B := not_le.mp h1
    by_cases h2 : hi ≤ sStar A B
    · have hcl : max lo (min (sStar A B) hi) = hi := by
        rw [min_eq_right h2, max_eq_right (le_trans hlo hhi)]
      rw [hcl]
      exact f_inc (s1 := s) (s2 := hi) hB (by linarith) hhi h2
    · have h2' : sStar A B < hi := not_le.mp h2
      have hcl : max lo (min (sStar A B) hi) = sStar A B := by
        rw [min_eq_left (le_of_lt h2'), max_eq_right (le_of_lt h1')]
      rw [hcl]
      by_cases h3 : s ≤ sStar A B
      · exact f_inc (s1 := s) (s2 := sStar A B) hB (by linarith) h3 le_rfl
      · exact f_dec (s1 := sStar A B) (s2 := s) hB (by linarith) le_rfl (le_of_lt (not_le.mp h3))

-- Axiom audit.
#print axioms Research.two_mul_le_sStar
#print axioms Research.f_diff_num
#print axioms Research.f_inc
#print axioms Research.f_dec
#print axioms Research.f_le_clamp

end Research
