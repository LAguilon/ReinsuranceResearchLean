/-
# Bounded claims — the three certificate cases over `ℝ`

Ports `Research/StopLossBounded.lean` to the real tier so the certificates can be
composed with the clamp lemma.  The rational tier stays authoritative for exact
witnesses; this file exists to be assembled into the unified theorem.

Also proves the variance-zero boundary: when `σ² = 0` the law is degenerate at
`μ`, so `E[(X-d)⁺] = (μ-d)⁺`.  That is what lets the unified theorem handle
`μ = M` (where `σ² ≤ μ(M-μ)` forces `σ² = 0`) without dividing by `M - μ`.
-/
import Research.Real.Sqrt

namespace Research

variable {ι : Type*} [Fintype ι]

/-! ## Case I — interior -/

/-- Pointwise interior majorant over `ℝ`. -/
theorem interior_majorant_R {s d x : ℝ} (_hs : 0 < s) :
    4 * s * max (x - d) 0 ≤ (x - d + s) ^ 2 := by
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg (x - d + s)]
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (x - d - s)]

/-- Interior bound over `ℝ`. -/
theorem stopLoss_bound_interior_R (L : FinLawR ι) (X : ι → ℝ) {μ d s σ2 : ℝ}
    (hs : 0 < s) (hsq : s ^ 2 = (μ - d) ^ 2 + σ2)
    (hone : L.IsProbability)
    (_hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2) :
    L.stopLossExpectation X d ≤ (μ - d + s) / 2 := by
  have h4 : 0 < 4 * s := by positivity
  have hsum : 4 * s * L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (X i - d + s) ^ 2 := by
    rw [FinLawR.stopLossExpectation, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have hp := interior_majorant_R (s := s) (d := d) (x := X i) hs
    have hm := L.nonneg i
    have hstep := mul_le_mul_of_nonneg_left hp hm
    nlinarith [hstep]
  have hrhs : (∑ i, L.mass i * (X i - d + s) ^ 2)
      = (-2 * (d - s)) * L.mean X + 1 * L.secondMoment X + (d - s) ^ 2 := by
    have h := FinLawR.sum_quadratic_const L X (-2 * (d - s)) 1 ((d - s) ^ 2) hone
    calc (∑ i, L.mass i * (X i - d + s) ^ 2)
        = ∑ i, L.mass i * ((-2 * (d - s)) * X i + 1 * (X i) ^ 2 + (d - s) ^ 2) := by
          congr 1 with i; ring
      _ = (-2 * (d - s)) * L.mean X + 1 * L.secondMoment X + (d - s) ^ 2 := h
  rw [hrhs, hmean, hsecond] at hsum
  have key : (-2 * (d - s)) * μ + 1 * (μ ^ 2 + σ2) + (d - s) ^ 2
      = 2 * s * (μ - d + s) := by
    nlinarith [hsq]
  rw [key] at hsum
  have hfinal : 4 * s * L.stopLossExpectation X d ≤ 4 * s * ((μ - d + s) / 2) := by
    nlinarith [hsum]
  exact le_of_mul_le_mul_left hfinal h4

/-! ## Case A — `a = 0` binds -/

/-- Pointwise certificate for case A over `ℝ`. -/
theorem atomZero_majorant_R {b0 d x : ℝ} (hb0 : 0 < b0) (hd : 0 ≤ d) (h2d : 2 * d ≤ b0)
    (hx : 0 ≤ x) :
    b0 ^ 2 * max (x - d) 0 ≤ d * x ^ 2 + (b0 ^ 2 - 2 * d * b0) * x := by
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    have hfac : 0 ≤ d * x + (b0 ^ 2 - 2 * d * b0) := by nlinarith
    nlinarith [mul_nonneg hx hfac]
  · rw [max_eq_left (by linarith)]
    nlinarith [mul_nonneg hd (sq_nonneg (x - b0))]

/-- Case A bound over `ℝ`. -/
theorem stopLoss_bound_atom_zero_R (L : FinLawR ι) (X : ι → ℝ) {μ d b0 σ2 : ℝ}
    (hμ : 0 < μ) (hb0 : μ * b0 = μ ^ 2 + σ2) (hb0pos : 0 < b0)
    (h2d : 2 * d ≤ b0) (hd : 0 ≤ d) (_hone : L.IsProbability)
    (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2) :
    L.stopLossExpectation X d ≤ μ * (b0 - d) / b0 := by
  have hb0sq : 0 < b0 ^ 2 := by positivity
  have hsum : b0 ^ 2 * L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (d * (X i) ^ 2 + (b0 ^ 2 - 2 * d * b0) * X i) := by
    rw [FinLawR.stopLossExpectation, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have hp := atomZero_majorant_R hb0pos hd h2d (hX i)
    have hm := L.nonneg i
    have hstep := mul_le_mul_of_nonneg_left hp hm
    nlinarith [hstep]
  have hrhs : (∑ i, L.mass i * (d * (X i) ^ 2 + (b0 ^ 2 - 2 * d * b0) * X i))
      = d * L.secondMoment X + (b0 ^ 2 - 2 * d * b0) * L.mean X := by
    have h := FinLawR.sum_quadratic L X (b0 ^ 2 - 2 * d * b0) d
    calc (∑ i, L.mass i * (d * (X i) ^ 2 + (b0 ^ 2 - 2 * d * b0) * X i))
        = ∑ i, L.mass i * ((b0 ^ 2 - 2 * d * b0) * X i + d * (X i) ^ 2) := by
          congr 1 with i; ring
      _ = (b0 ^ 2 - 2 * d * b0) * L.mean X + d * L.secondMoment X := h
      _ = d * L.secondMoment X + (b0 ^ 2 - 2 * d * b0) * L.mean X := by ring
  rw [hrhs, hmean, hsecond] at hsum
  have key : d * (μ ^ 2 + σ2) + (b0 ^ 2 - 2 * d * b0) * μ = μ * b0 * (b0 - d) := by
    nlinarith [hb0]
  rw [key] at hsum
  have hfinal : b0 ^ 2 * L.stopLossExpectation X d ≤ b0 ^ 2 * (μ * (b0 - d) / b0) := by
    have hdiv : b0 ^ 2 * (μ * (b0 - d) / b0) = μ * b0 * (b0 - d) := by field_simp
    nlinarith [hsum, hdiv]
  exact le_of_mul_le_mul_left hfinal hb0sq

/-! ## Case B — `b = M` binds -/

/-- Pointwise certificate for case B over `ℝ`. -/
theorem atomTop_majorant_R {M d a1 c x : ℝ} (hc : 0 < c) (hxM : x ≤ M)
    (hcx : c * (M - a1) ^ 2 = M - d) (hslope : 2 * c * (M - a1) ≤ 1)
    (ha1d : a1 ≤ d) :
    max (x - d) 0 ≤ c * (x - a1) ^ 2 := by
  have hfac : c * (x - a1) ^ 2 - (x - d)
      = (x - M) * (c * (x - M) + (2 * c * (M - a1) - 1)) := by
    nlinarith [hcx]
  have hprod : 0 ≤ (x - M) * (c * (x - M) + (2 * c * (M - a1) - 1)) := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · linarith
    · nlinarith [hslope, hc, hxM]
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    positivity
  · rw [max_eq_left (by linarith)]
    linarith [hfac]

/-- Case B bound over `ℝ`. -/
theorem stopLoss_bound_atom_top_R (L : FinLawR ι) (X : ι → ℝ) {μ d a1 c σ2 M : ℝ}
    (hM : 0 < M) (ha1 : 0 ≤ a1) (ha1d : a1 ≤ d) (hdM : d ≤ M)
    (hc : 0 < c) (hcM : c * (M - a1) ^ 2 = M - d)
    (hslope : 2 * c * (M - a1) ≤ 1) (hMa1 : 0 < M - a1)
    (hone : L.IsProbability) (_hX : ∀ i, 0 ≤ X i) (hXM : ∀ i, X i ≤ M)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2)
    (hmom : (μ - a1) * (M - a1) = (μ - a1) ^ 2 + σ2) :
    L.stopLossExpectation X d ≤ (M - d) * (μ - a1) / (M - a1) := by
  have hsum : L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (c * (X i - a1) ^ 2) := by
    rw [FinLawR.stopLossExpectation]
    refine Finset.sum_le_sum ?_
    intro i _
    have hp := atomTop_majorant_R (M := M) (d := d) (a1 := a1) (c := c) (x := X i)
      hc (hXM i) hcM hslope ha1d
    have hm := L.nonneg i
    nlinarith [mul_le_mul_of_nonneg_left hp hm]
  have hexp : (∑ i, L.mass i * (c * (X i - a1) ^ 2))
      = c * ((μ - a1) ^ 2 + σ2) := by
    have h : ∀ i, L.mass i * (c * (X i - a1) ^ 2)
        = c * (L.mass i * ((-2 * a1) * X i + 1 * (X i) ^ 2 + a1 ^ 2)) := by
      intro i; ring
    simp only [h, ← Finset.mul_sum]
    rw [FinLawR.sum_quadratic_const L X (-2 * a1) 1 (a1 ^ 2) hone, hmean, hsecond]
    ring
  rw [hexp, ← hmom] at hsum
  have hcdiv : c * (M - a1) = (M - d) / (M - a1) := by
    field_simp
    nlinarith [hcM]
  have hval : c * ((μ - a1) * (M - a1)) = (M - d) * (μ - a1) / (M - a1) := by
    calc c * ((μ - a1) * (M - a1)) = (μ - a1) * (c * (M - a1)) := by ring
      _ = (μ - a1) * ((M - d) / (M - a1)) := by rw [hcdiv]
      _ = (M - d) * (μ - a1) / (M - a1) := by ring
  linarith [hsum, hval]

/-! ## Variance-zero boundary -/

/-- **Degenerate case.**  If `σ² = 0` then `X = μ` on the support, so the stop-loss
expectation is exactly `(μ - d)⁺`.  This is what removes the `M - μ = 0` division
from the unified theorem. -/
theorem stopLoss_variance_zero (L : FinLawR ι) (X : ι → ℝ) {μ d : ℝ}
    (hone : L.IsProbability) (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2) :
    L.stopLossExpectation X d = max (μ - d) 0 := by
  have hvar : (∑ i, L.mass i * (X i - μ) ^ 2) = 0 := by
    have h : ∀ i, L.mass i * (X i - μ) ^ 2
        = L.mass i * (X i) ^ 2 + (-2 * μ) * (L.mass i * X i) + μ ^ 2 * L.mass i := by
      intro i; ring
    simp only [h, Finset.sum_add_distrib, Finset.sum_mul, ← Finset.mul_sum]
    have hm' : (∑ i, L.mass i * X i) = μ := hmean
    have hs' : (∑ i, L.mass i * (X i) ^ 2) = μ ^ 2 := hsecond
    rw [hm', hs', hone]
    ring
  have hterm : ∀ i, L.mass i * (X i - μ) ^ 2 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (L.nonneg j) (sq_nonneg (X j - μ)))).mp hvar i (Finset.mem_univ i)
  have hXi : ∀ i, L.mass i ≠ 0 → X i = μ := by
    intro i hi
    have h := hterm i
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 hi
    · nlinarith [sq_nonneg (X i - μ)]
  have hcongr : L.stopLossExpectation X d = ∑ i, L.mass i * max (μ - d) 0 := by
    rw [FinLawR.stopLossExpectation]
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases hi : L.mass i = 0
    · simp [hi]
    · rw [hXi i hi]
  rw [hcongr, ← Finset.sum_mul, hone, one_mul]

-- Axiom audit.
#print axioms Research.interior_majorant_R
#print axioms Research.stopLoss_bound_interior_R
#print axioms Research.atomZero_majorant_R
#print axioms Research.stopLoss_bound_atom_zero_R
#print axioms Research.atomTop_majorant_R
#print axioms Research.stopLoss_bound_atom_top_R
#print axioms Research.stopLoss_variance_zero

end Research
