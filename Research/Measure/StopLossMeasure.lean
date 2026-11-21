/-
# Stop-loss bound for arbitrary probability measures

Removes the finite-support restriction: `X` is an arbitrary real random variable
on a probability space with `MemLp X 2 P`.

Interior (R2) case only. The bounded/unbounded dispatchers are not ported.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

open MeasureTheory

namespace Research

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Pointwise majorant, valid for **all** real `x`. -/
theorem interior_majorant_all {s d x : ℝ} (_hs : 0 < s) :
    4 * s * max (x - d) 0 ≤ (x - d + s) ^ 2 := by
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg (x - d + s)]
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (x - d - s)]

/-- **T1.**  Measure-theoretic interior stop-loss bound. -/
theorem integral_stopLoss_le [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) {μ d s σ2 : ℝ} (hs : 0 < s)
    (hsq : s ^ 2 = (μ - d) ^ 2 + σ2)
    (hmean : ∫ x, X x ∂P = μ) (hsecond : ∫ x, (X x) ^ 2 ∂P = μ ^ 2 + σ2) :
    ∫ x, max (X x - d) 0 ∂P ≤ (μ - d + s) / 2 := by
  have hs4 : 0 < 4 * s := by positivity
  have hXint : Integrable X P := hX.integrable (by norm_num)
  have hX2 : Integrable (fun x => (X x) ^ 2) P := hX.integrable_sq
  have hlin : Integrable (fun x => 2 * (d - s) * X x) P := hXint.const_mul _
  have hquad : Integrable (fun x => (X x) ^ 2 - 2 * (d - s) * X x) P := hX2.sub hlin
  have hconst : Integrable (fun _ : Ω => (d - s) ^ 2) P := integrable_const _
  have hsqint : Integrable (fun x => (X x - d + s) ^ 2) P := by
    refine (hquad.add hconst).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  have hrhs : Integrable (fun x => (X x - d + s) ^ 2 / (4 * s)) P := by
    have h := hsqint.const_mul ((4 * s)⁻¹)
    refine h.congr ?_
    filter_upwards with x
    rw [div_eq_inv_mul]
  have hnonneg : 0 ≤ᵐ[P] fun x => max (X x - d) 0 :=
    Filter.Eventually.of_forall (fun x => le_max_right _ _)
  have hle : (fun x => max (X x - d) 0) ≤ᵐ[P]
      fun x => (X x - d + s) ^ 2 / (4 * s) := by
    filter_upwards with x
    rw [le_div_iff₀ hs4]
    linarith [interior_majorant_all (s := s) (d := d) (x := X x) hs]
  have hmono := integral_mono_of_nonneg hnonneg hrhs hle
  have hval : ∫ x, (X x - d + s) ^ 2 / (4 * s) ∂P = (μ - d + s) / 2 := by
    have h1 : (fun x => (X x - d + s) ^ 2 / (4 * s))
        = fun x => (4 * s)⁻¹ * (X x - d + s) ^ 2 := by
      funext x; rw [div_eq_inv_mul]
    rw [h1, integral_const_mul]
    have h2 : ∫ x, (X x - d + s) ^ 2 ∂P = 2 * s * (μ - d + s) := by
      have hcongr : (fun x => (X x - d + s) ^ 2)
          = fun x => ((X x) ^ 2 - 2 * (d - s) * X x) + (d - s) ^ 2 := by
        funext x; ring_nf
      rw [hcongr, integral_add hquad hconst, integral_sub hX2 hlin,
          integral_const_mul, integral_const, hmean, hsecond]
      have huniv : P.real Set.univ = 1 := by simp
      rw [huniv, one_smul]
      nlinarith [hsq]
    rw [h2]
    field_simp
    ring
  rw [hval] at hmono
  exact hmono

end Research
