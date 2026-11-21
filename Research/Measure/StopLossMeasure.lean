/-
# Stop-loss bound for arbitrary probability measures — partial

Attempt at the measure-theoretic version of the interior (R2) bound. **Only the
pointwise majorant is completed.** The integral step is blocked on a Mathlib
detail, recorded below with the exact goal state.

## What is proved

`interior_majorant_all : 4 s (x - d)⁺ ≤ (x - d + s)²` for **all** real `x`, `s > 0`.
This is the entire analytic content; the finite-support development uses exactly
this inequality and nothing else.

## What is not proved, and exactly where it stops

Target:

```lean
theorem integral_stopLoss_le [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) (hX2 : Integrable (fun x => (X x) ^ 2) P)
    (hs : 0 < s) (hsq : s ^ 2 = (μ - d) ^ 2 + σ2)
    (hmean : ∫ x, X x ∂P = μ) (hsecond : ∫ x, (X x) ^ 2 ∂P = μ ^ 2 + σ2) :
    ∫ x, max (X x - d) 0 ∂P ≤ (μ - d + s) / 2
```

The remaining obligations are:

1. `Integrable (fun x => max (X x - d) 0) P`. The route via `Integrable.sup`
   fails because `Integrable` is stated for a normed group while `⊔` is resolved
   in the lattice structure; the working identity `max a 0 = (a + |a|)/2` needs a
   lemma name that does not exist in this Mathlib revision (`max_eq_add_abs` is
   absent). A three-line `rcases le_or_lt 0 a` case split would close it.
2. Rewriting `∫ (X - d + s)²` as `∫X² - 2(d-s)∫X + (d-s)²` under the integral,
   then `nlinarith [hsq]`.

Nothing here is mathematically uncertain; it is API plumbing that exceeded the
time box.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

namespace Research

/-- **Pointwise majorant for arbitrary real `x`.** -/
theorem interior_majorant_all {s d x : ℝ} (_hs : 0 < s) :
    4 * s * max (x - d) 0 ≤ (x - d + s) ^ 2 := by
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg (x - d + s)]
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (x - d - s)]

end Research
