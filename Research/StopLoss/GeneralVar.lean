/-
# Unbounded claims — the general-σ² stop-loss bound on `[0, ∞)`

The `M → ∞` limit of the bounded problem: the `b = M` branch disappears, and the
supremum is

  `sup E[(X-d)⁺] = f A σ² (min s* μ)`,   `A = μ - d`,  `s* = A + √(A²+σ²)`,

with the two remaining regimes already covered by the bounded development:
`t ≤ μ` is the interior certificate, `μ < t` is the `a = 0` certificate.

No upper bound on the claims is assumed; only `X ≥ 0`, `E[X] = μ`, `Var X = σ²`.
-/
import Research.StopLoss.BoundedUnified

namespace Research

variable {ι : Type*} [Fintype ι]

/-- **Unbounded, interior regime** (`s* ≤ μ`). -/
theorem bound_unbounded_interior (L : FinLawR ι) (X : ι → ℝ) {μ σ2 d : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ2) (_hd0 : 0 ≤ d) (hone : L.IsProbability) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2)
    (ht : sStar (μ - d) σ2 ≤ μ) :
    L.stopLossExpectation X d
      ≤ max 0 (f (μ - d) σ2 (min (sStar (μ - d) σ2) μ)) := by
  have hcl : min (sStar (μ - d) σ2) μ = sStar (μ - d) σ2 := min_eq_left ht
  rw [hcl]
  set r := Real.sqrt ((μ - d) ^ 2 + σ2) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrsq : r ^ 2 = (μ - d) ^ 2 + σ2 := Real.sq_sqrt (by positivity)
  have hbound := stopLoss_bound_interior_R L X (μ := μ) (d := d) (s := r) (σ2 := σ2)
    hrpos hrsq hone hX hmean hsecond
  have htr : sStar (μ - d) σ2 = (μ - d) + r := by rw [sStar, ← hr]
  have hval : (μ - d + r) / 2 = f (μ - d) σ2 (sStar (μ - d) σ2) := by
    rw [htr]
    exact (f_sStar (A := μ - d) (B := σ2) hσ).symm
  rw [hval] at hbound
  exact le_trans hbound (le_max_right 0 _)

/-- **Unbounded, `a = 0` regime** (`μ < s*`). -/
theorem bound_unbounded_atom_zero (L : FinLawR ι) (X : ι → ℝ) {μ σ2 d : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ2) (hd0 : 0 ≤ d) (hone : L.IsProbability) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2)
    (ht : μ < sStar (μ - d) σ2) :
    L.stopLossExpectation X d
      ≤ max 0 (f (μ - d) σ2 (min (sStar (μ - d) σ2) μ)) := by
  have hcl : min (sStar (μ - d) σ2) μ = μ := min_eq_right (le_of_lt ht)
  rw [hcl]
  set b0 := (μ ^ 2 + σ2) / μ with hb0
  have hb0pos : 0 < b0 := by rw [hb0]; positivity
  have hb0eq : μ * b0 = μ ^ 2 + σ2 := by rw [hb0]; field_simp
  have h2d : 2 * d ≤ b0 := by
    rw [hb0]
    exact coverage_atom_zero (A := μ - d) (B := σ2) (μ := μ) (d := d) hσ rfl hμ hd0
      (le_of_lt ht)
  have hbound := stopLoss_bound_atom_zero_R L X (μ := μ) (d := d) (b0 := b0) (σ2 := σ2)
    (hμ := hμ) (hb0 := hb0eq) (hb0pos := hb0pos) (h2d := h2d) (hd := hd0)
    (_hone := hone) (hX := hX) (hmean := hmean) (hsecond := hsecond)
  have hval : μ * (b0 - d) / b0 = f (μ - d) σ2 μ := by
    rw [hb0]
    have h1 : μ * ((μ ^ 2 + σ2) / μ - d) / ((μ ^ 2 + σ2) / μ)
        = μ * (1 - d / ((μ ^ 2 + σ2) / μ)) := by
      field_simp
    rw [h1]
    exact (f_mu (A := μ - d) (B := σ2) (μ := μ) (d := d) hμ (le_of_lt hσ) rfl).symm
  rw [hval] at hbound
  exact le_trans hbound (le_max_right 0 _)

/-- **General-σ² unbounded stop-loss bound.** -/
theorem stopLoss_bound_unbounded (L : FinLawR ι) (X : ι → ℝ) {μ σ2 d : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ2) (hd0 : 0 ≤ d) (hone : L.IsProbability) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2) :
    L.stopLossExpectation X d
      ≤ max 0 (f (μ - d) σ2 (min (sStar (μ - d) σ2) μ)) := by
  by_cases h : sStar (μ - d) σ2 ≤ μ
  · exact bound_unbounded_interior L X hμ hσ hd0 hone hX hmean hsecond h
  · exact bound_unbounded_atom_zero L X hμ hσ hd0 hone hX hmean hsecond (not_le.mp h)

#print axioms Research.bound_unbounded_interior
#print axioms Research.bound_unbounded_atom_zero
#print axioms Research.stopLoss_bound_unbounded

end Research
