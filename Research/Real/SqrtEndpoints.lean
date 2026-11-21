/-
# Real tier — endpoint identities and coverage lemmas

Slice 1 of the unified bounded-claims theorem.

With `A = μ - d`, `B = σ² > 0`, `t = s* = A + √(A²+B)` and `ht : t² = 2At + B`:

* `s* > 0`;
* `f A B t = t/2`;
* `f A B μ = μ(1 - d/b₀)`, `b₀ = (μ²+B)/μ`;
* `f A B lo = (M-d)(μ-a₁)/(M-a₁)`, `lo = B/(M-μ)`;
* `t ≥ μ → b₀ ≥ 2d`;
* `t ≤ lo → 2(M-d) ≤ M-μ+lo`.
-/
import Research.StopLoss.BoundedReal

namespace Research

/-- `s* > 0`. -/
theorem sStar_pos {A B : ℝ} (hB : 0 < B) : 0 < sStar A B := by
  have hr : 0 < Real.sqrt (A ^ 2 + B) := Real.sqrt_pos.mpr (by positivity)
  have hr2 : (Real.sqrt (A ^ 2 + B)) ^ 2 = A ^ 2 + B := Real.sq_sqrt (by positivity)
  by_cases hA : A ≤ 0
  · have hneg : 0 ≤ -A := by linarith
    have hsq : (-A) ^ 2 < (Real.sqrt (A ^ 2 + B)) ^ 2 := by rw [hr2]; nlinarith
    have hlt : -A < Real.sqrt (A ^ 2 + B) := by nlinarith [hsq, hneg, le_of_lt hr]
    unfold sStar
    linarith
  · have hpos : 0 < A := by linarith
    unfold sStar
    linarith

/-- **Interior endpoint.**  `f A B s* = s*/2`. -/
theorem f_sStar {A B : ℝ} (hB : 0 < B) :
    f A B (sStar A B) = sStar A B / 2 := by
  have ht : (sStar A B) ^ 2 = 2 * A * sStar A B + B := sStar_sq (le_of_lt hB)
  have hfac : 2 * A * (sStar A B) ^ 2 + (sStar A B) * B - (sStar A B) ^ 3
      = (sStar A B) * (2 * A * sStar A B + B - (sStar A B) ^ 2) := by ring
  have hzero : 2 * A * (sStar A B) ^ 2 + (sStar A B) * B - (sStar A B) ^ 3 = 0 := by
    rw [hfac, ht]; ring
  have hden : (sStar A B) ^ 2 + B ≠ 0 := by nlinarith [sq_nonneg (sStar A B), hB]
  unfold f
  field_simp
  linarith [hzero]

/-- **Case A endpoint.**  `f A B μ = μ (1 - d/b₀)`. -/
theorem f_mu {A B μ d : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) (hA : A = μ - d) :
    f A B μ = μ * (1 - d / ((μ ^ 2 + B) / μ)) := by
  subst hA
  have hden : μ ^ 2 + B ≠ 0 := by nlinarith [sq_nonneg μ, hB]
  unfold f
  field_simp
  ring

/-- **Case B endpoint.**  `f A B lo = (M-d)(μ-a₁)/(M-a₁)` with `lo = B/(M-μ)`. -/
theorem f_lo {A B M μ d : ℝ} (hμM : μ < M) (hB : 0 < B) (hA : A = μ - d) :
    f A B (B / (M - μ)) = (M - d) * (B / (M - μ)) / (M - μ + B / (M - μ)) := by
  subst hA
  have hu : 0 < M - μ := by linarith
  have h1 : 0 < B / (M - μ) := div_pos hB hu
  have hden1 : (B / (M - μ)) ^ 2 + B ≠ 0 := by nlinarith [sq_nonneg (B / (M - μ)), h1]
  have hden2 : M - μ + B / (M - μ) ≠ 0 := by linarith
  unfold f
  field_simp
  ring

/-- **Coverage 2a.**  `t ≥ μ → b₀ ≥ 2d`. -/
theorem coverage_atom_zero {A B μ d : ℝ} (hB : 0 < B) (hA : A = μ - d)
    (hμ : 0 < μ) (hd : 0 ≤ d) (htμ : μ ≤ sStar A B) :
    2 * d ≤ (μ ^ 2 + B) / μ := by
  have ht : (sStar A B) ^ 2 = 2 * A * sStar A B + B := sStar_sq (le_of_lt hB)
  have hfac : μ ^ 2 + B - 2 * μ * d = (sStar A B - μ) * (sStar A B - μ + 2 * d) := by
    nlinarith [ht, hA]
  have h1 : 0 ≤ sStar A B - μ := by linarith
  have h2 : 0 ≤ sStar A B - μ + 2 * d := by linarith
  have h3 : 0 ≤ μ ^ 2 + B - 2 * μ * d := by rw [hfac]; exact mul_nonneg h1 h2
  rw [le_div_iff₀ hμ]
  linarith

/-- **Coverage 2b.**  `t ≤ B/(M-μ) → 2(M-d) ≤ M-μ + B/(M-μ)`. -/
theorem coverage_atom_top {A B M μ d : ℝ} (hB : 0 < B) (hA : A = μ - d)
    (hμM : μ < M) (htlo : sStar A B ≤ B / (M - μ)) :
    2 * (M - d) ≤ M - μ + B / (M - μ) := by
  have ht : (sStar A B) ^ 2 = 2 * A * sStar A B + B := sStar_sq (le_of_lt hB)
  have htpos : 0 < sStar A B := sStar_pos hB
  have hu : 0 < M - μ := by linarith
  have h1 : sStar A B * (M - μ) ≤ B := by
    rw [le_div_iff₀ hu] at htlo
    exact htlo
  have h2 : 0 ≤ sStar A B - 2 * A - (M - μ) := by
    by_cases h : 0 ≤ sStar A B - 2 * A - (M - μ)
    · exact h
    · have hlt : sStar A B - 2 * A - (M - μ) < 0 := not_le.mp h
      have hneg : sStar A B * (sStar A B - 2 * A - (M - μ)) < 0 := by nlinarith [hlt, htpos]
      nlinarith [ht, h1, hneg]
  have hfac : B - ((M - μ) ^ 2 + 2 * A * (M - μ))
      = (sStar A B + (M - μ)) * (sStar A B - 2 * A - (M - μ)) := by
    nlinarith [ht]
  have hpos : 0 ≤ sStar A B + (M - μ) := by linarith
  have h3 : (M - μ) ^ 2 + 2 * A * (M - μ) ≤ B := by
    nlinarith [hfac, mul_nonneg hpos h2]
  have h4 : (M - μ) + 2 * A ≤ B / (M - μ) := by
    rw [le_div_iff₀ hu]
    nlinarith [h3]
  linarith

-- Axiom audit.
#print axioms Research.sStar_pos
#print axioms Research.f_sStar
#print axioms Research.f_mu
#print axioms Research.f_lo
#print axioms Research.coverage_atom_zero
#print axioms Research.coverage_atom_top

end Research
