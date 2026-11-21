/-
# Bounded claims — branch lemmas for the unified theorem

Slice 2a: the interior branch.
-/
import Research.Real.SqrtEndpoints

namespace Research

variable {ι : Type*} [Fintype ι]

/-- **Interior branch.**  When `lo ≤ s* ≤ μ` the clamp is `s*` and the interior
certificate applies with parameter `r = √((μ-d)²+σ²)`. -/
theorem bound_interior_branch (L : FinLawR ι) (X : ι → ℝ) {M μ σ2 d : ℝ}
    (hμ : 0 < μ) (hμM : μ ≤ M) (hd0 : 0 ≤ d) (hdM : d ≤ M) (hσ : 0 < σ2)
    (hone : L.IsProbability) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2)
    (hlo_t : σ2 / (M - μ) ≤ sStar (μ - d) σ2)
    (ht_μ : sStar (μ - d) σ2 ≤ μ) :
    L.stopLossExpectation X d
      ≤ max 0 (f (μ - d) σ2 (max (σ2 / (M - μ)) (min (sStar (μ - d) σ2) μ))) := by
  have hcl : max (σ2 / (M - μ)) (min (sStar (μ - d) σ2) μ) = sStar (μ - d) σ2 := by
    rw [min_eq_left ht_μ, max_eq_right hlo_t]
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

#print axioms Research.bound_interior_branch

/-- **Case A branch.**  When `μ < s*` the clamp is `μ` and the `a = 0`
certificate applies with `b₀ = (μ²+σ²)/μ`. -/
theorem bound_atom_zero_branch (L : FinLawR ι) (X : ι → ℝ) {M μ σ2 d : ℝ}
    (hμ : 0 < μ) (hμM : μ < M) (hd0 : 0 ≤ d) (hdM : d ≤ M) (hσ : 0 < σ2)
    (hσmax : σ2 ≤ μ * (M - μ))
    (hone : L.IsProbability) (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2)
    (hμ_t : μ < sStar (μ - d) σ2) :
    L.stopLossExpectation X d
      ≤ max 0 (f (μ - d) σ2 (max (σ2 / (M - μ)) (min (sStar (μ - d) σ2) μ))) := by
  have hu : 0 < M - μ := by linarith
  have hloμ : σ2 / (M - μ) ≤ μ := by
    rw [div_le_iff₀ hu]; linarith
  have hcl : max (σ2 / (M - μ)) (min (sStar (μ - d) σ2) μ) = μ := by
    rw [min_eq_right (le_of_lt hμ_t), max_eq_right hloμ]
  rw [hcl]
  set b0 := (μ ^ 2 + σ2) / μ with hb0
  have hb0pos : 0 < b0 := by rw [hb0]; positivity
  have hb0eq : μ * b0 = μ ^ 2 + σ2 := by rw [hb0]; field_simp
  have h2d : 2 * d ≤ b0 := by
    rw [hb0]
    exact coverage_atom_zero (A := μ - d) (B := σ2) (μ := μ) (d := d) hσ rfl hμ hd0
      (le_of_lt hμ_t)
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

#print axioms Research.bound_atom_zero_branch

/-- **Case B branch.**  When `s* < lo` the clamp is `lo` and the `b = M`
certificate applies with lower atom `a₁ = μ - lo`. -/
theorem bound_atom_top_branch (L : FinLawR ι) (X : ι → ℝ) {M μ σ2 d : ℝ}
    (hμ : 0 < μ) (hμM : μ < M) (hd0 : 0 ≤ d) (hdM : d < M) (hσ : 0 < σ2)
    (hσmax : σ2 ≤ μ * (M - μ))
    (hone : L.IsProbability) (hX : ∀ i, 0 ≤ X i) (hXM : ∀ i, X i ≤ M)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2)
    (ht_lo : sStar (μ - d) σ2 < σ2 / (M - μ)) :
    L.stopLossExpectation X d
      ≤ max 0 (f (μ - d) σ2 (max (σ2 / (M - μ)) (min (sStar (μ - d) σ2) μ))) := by
  have hu : 0 < M - μ := by linarith
  have hloμ : σ2 / (M - μ) ≤ μ := by
    rw [div_le_iff₀ hu]; linarith
  have htμ : sStar (μ - d) σ2 ≤ μ := le_trans (le_of_lt ht_lo) hloμ
  have hcl : max (σ2 / (M - μ)) (min (sStar (μ - d) σ2) μ) = σ2 / (M - μ) := by
    rw [min_eq_left htμ, max_eq_left (le_of_lt ht_lo)]
  rw [hcl]
  set lo := σ2 / (M - μ) with hlo
  set a1 := μ - lo with ha1
  have ha1nonneg : 0 ≤ a1 := by rw [ha1]; linarith
  have ha1d : a1 ≤ d := by
    rw [ha1]
    have hgt : μ - d < sStar (μ - d) σ2 := sStar_gt hσ
    linarith
  have hMa1 : 0 < M - a1 := by rw [ha1]; linarith
  set c := (M - d) / (M - a1) ^ 2 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcM : c * (M - a1) ^ 2 = M - d := by rw [hc]; field_simp
  have hcov : 2 * (M - d) ≤ M - a1 := by
    have h := coverage_atom_top (A := μ - d) (B := σ2) (M := M) (μ := μ) (d := d)
      hσ rfl hμM (le_of_lt ht_lo)
    rw [← hlo] at h
    rw [ha1]
    have : M - (μ - lo) = M - μ + lo := by ring
    rw [this]
    exact h
  have hslope : 2 * c * (M - a1) ≤ 1 := by
    rw [hc]
    have hslope_eq : 2 * ((M - d) / (M - a1) ^ 2) * (M - a1) = 2 * (M - d) / (M - a1) := by
      field_simp
    rw [hslope_eq, div_le_one hMa1]
    exact hcov
  have hmem : (μ - a1) * (M - a1) = (μ - a1) ^ 2 + σ2 := by
    have h1 : μ - a1 = lo := by rw [ha1]; ring
    have h2 : σ2 = lo * (M - μ) := by rw [hlo]; field_simp
    have h3 : M - a1 = M - μ + lo := by rw [ha1]; ring
    rw [h1, h2, h3]; ring
  have hbound := stopLoss_bound_atom_top_R L X (μ := μ) (d := d) (a1 := a1) (c := c)
    (σ2 := σ2) (M := M) (by linarith) ha1nonneg ha1d (le_of_lt hdM) hcpos hcM hslope
    hMa1 hone hX hXM hmean hsecond hmem
  have hval : (M - d) * (μ - a1) / (M - a1) = f (μ - d) σ2 lo := by
    have h1 : μ - a1 = lo := by rw [ha1]; ring
    have h2 : M - a1 = M - μ + lo := by rw [ha1]; ring
    rw [h1, h2]
    have h3 := (f_lo (A := μ - d) (B := σ2) (M := M) (μ := μ) (d := d) hμM hσ rfl).symm
    rw [← hlo] at h3
    exact h3
  rw [hval] at hbound
  exact le_trans hbound (le_max_right 0 _)

#print axioms Research.bound_atom_top_branch

/-- **Unified bounded-claims bound.**  Over the closed feasibility region, every
finite law supported in `[0, M]` with the stated moments satisfies
`E[(X-d)⁺] ≤ max 0 (f A σ² (clamp(s*, σ²/(M-μ), μ)))`. -/
theorem stopLoss_bound_bounded (L : FinLawR ι) (X : ι → ℝ) {M μ σ2 d : ℝ}
    (hM : 0 < M) (hμ0 : 0 ≤ μ) (hμM : μ ≤ M) (hd0 : 0 ≤ d) (hdM : d ≤ M)
    (hσ0 : 0 ≤ σ2) (hσmax : σ2 ≤ μ * (M - μ))
    (hone : L.IsProbability) (hX : ∀ i, 0 ≤ X i) (hXM : ∀ i, X i ≤ M)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2) :
    L.stopLossExpectation X d
      ≤ max 0 (f (μ - d) σ2 (max (σ2 / (M - μ)) (min (sStar (μ - d) σ2) μ))) := by
  rcases eq_or_lt_of_le hdM with hdM_eq | hdM_lt
  · -- d = M: the payoff vanishes
    rw [hdM_eq]
    have hzero : L.stopLossExpectation X M = 0 := by
      rw [FinLawR.stopLossExpectation]
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [max_eq_right (by linarith [hXM i])]
      ring
    rw [hzero]
    exact le_max_left 0 _
  · rcases eq_or_lt_of_le hσ0 with hσ_eq | hσ_pos
    · -- σ² = 0
      subst hσ_eq
      have hsecond' : L.secondMoment X = μ ^ 2 := by simpa using hsecond
      rw [stopLoss_variance_zero L X hone hmean hsecond']
      have hf : f (μ - d) 0 (max (0 / (M - μ)) (min (sStar (μ - d) 0) μ)) = μ - d := by
        simp [f]
      rw [hf]
      exact le_of_eq (max_comm (μ - d) 0)
    · -- σ² > 0: three branches
      have hμpos : 0 < μ := by
        rcases eq_or_lt_of_le hμ0 with h | h
        · subst h; nlinarith [hσmax]
        · exact h
      have hu : 0 < M - μ := by
        rcases eq_or_lt_of_le hμM with h | h
        · subst h; nlinarith [hσmax]
        · linarith
      by_cases h1 : sStar (μ - d) σ2 < σ2 / (M - μ)
      · exact bound_atom_top_branch L X hμpos (by linarith) hd0 hdM_lt hσ_pos hσmax hone
          hX hXM hmean hsecond h1
      · have h2 : σ2 / (M - μ) ≤ sStar (μ - d) σ2 := not_lt.mp h1
        by_cases h3 : sStar (μ - d) σ2 ≤ μ
        · exact bound_interior_branch L X hμpos hμM hd0 hdM hσ_pos hone hX hmean hsecond h2 h3
        · exact bound_atom_zero_branch L X hμpos (by linarith) hd0 hdM hσ_pos hσmax hone
            hX hmean hsecond (not_le.mp h3)

#print axioms Research.stopLoss_bound_bounded




end Research
