/-
# Stage C — bounded claims: the interior (R2) regime, kernel-checked

Companion to `research/trackA-bounded.md`.  The bounded-claims problem on `[0, M]`
splits into four regimes; this file formalises the interior one, where the dual
certificate is a perfect square.

**Theorem (`stopLoss_bound_interior`).**  Let `s > 0` with
`s² = (μ - d)² + σ²`.  For any finite law on `[0, ∞)` with total mass one,
`E[X] = μ` and `E[X²] = μ² + σ²`,

  `E[(X - d)⁺] ≤ (μ - d + s)/2`.

The proof is the pointwise majorant

  `4 s (x - d)⁺ ≤ (x - d + s)²`,   slack `(x - d - s)²` above the kink,

summed against the weights.  The regime condition of the Stage B note
(`s ≤ d` and `d + s ≤ M`) is what makes the bound *attained*, by the two-atom law
`{d - s, d + s}`; attainment is exhibited concretely at the end of the file.

Status: `PARTIAL` — this is one regime of the bounded problem.  The remaining
regimes (R1, R3, R4) are not formalised here; R1 provably admits no quadratic
certificate.
-/
import Research.StopLoss

namespace Research

variable {ι : Type*} [Fintype ι]

namespace FinLaw

/-- Total mass one.  Needed only when the majorant carries a constant term. -/
def IsProbability (L : FinLaw ι) : Prop := ∑ i, L.mass i = 1

/-- Pulling-out lemma for a quadratic *with constant term*. -/
lemma sum_quadratic_const (L : FinLaw ι) (X : ι → ℚ) (a b c : ℚ)
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

end FinLaw

/-- **Pointwise interior majorant.**  For `s > 0` and every `x`,

  `4 s (x - d)⁺ ≤ (x - d + s)²`,

with equality iff `x = d + s` or `x ≤ d`. -/
theorem interior_majorant {s d x : ℚ} (_hs : 0 < s) :
    4 * s * max (x - d) 0 ≤ (x - d + s) ^ 2 := by
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    have hsq : (0 : ℚ) ≤ (x - d + s) ^ 2 := sq_nonneg _
    nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (x - d - s)]

/-- **Interior stop-loss bound (regime R2).** -/
theorem stopLoss_bound_interior (L : FinLaw ι) (X : ι → ℚ) {μ d s σ2 : ℚ}
    (hs : 0 < s) (hsq : s ^ 2 = (μ - d) ^ 2 + σ2)
    (hone : L.IsProbability)
    (_hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2) :
    L.stopLossExpectation X d ≤ (μ - d + s) / 2 := by
  have h4 : 0 < 4 * s := by positivity
  -- multiply the pointwise majorant by the mass and sum
  have hsum : 4 * s * L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (X i - d + s) ^ 2 := by
    rw [FinLaw.stopLossExpectation, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have hp := interior_majorant (s := s) (d := d) (x := X i) hs
    have hm := L.nonneg i
    have hstep := mul_le_mul_of_nonneg_left hp hm
    nlinarith [hstep]
  -- evaluate the right-hand side with the moment constraints
  have hrhs : (∑ i, L.mass i * (X i - d + s) ^ 2)
      = (-2 * (d - s)) * L.mean X + 1 * L.secondMoment X + (d - s) ^ 2 := by
    have h := FinLaw.sum_quadratic_const L X (-2 * (d - s)) 1 ((d - s) ^ 2) hone
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

/-! ## Sharpness at a rational instance

`M = 1`, `μ = 1/2`, `σ² = 1/16`, `d = 1/2`, `s = 1/4`: the theorem gives
`E[(X - 1/2)⁺] ≤ 1/8`, and the two-atom law `{1/4, 3/4}` with mass `1/2` each
attains it.  This is the non-vacuity and sharpness witness for the regime. -/

/-- Mass vector on `Bool`: `p` at `true`, `1 - p` at `false`. -/
def twoAtomMass (p : ℚ) : Bool → ℚ := fun b => if b then p else 1 - p

/-- Claim vector on `Bool`: `b` at `true`, `a` at `false`. -/
def twoAtomClaim (a b : ℚ) : Bool → ℚ := fun t => if t then b else a

/-- The two-atom law with mass `p` on the upper atom. -/
def twoAtomLaw (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinLaw Bool :=
  ⟨twoAtomMass p, by
    intro i
    cases i <;> simp [twoAtomMass] <;> linarith⟩

/-- **Sharpness witness.**  The law `{1/4, 3/4}` with mass `1/2` each has mean
`1/2`, second moment `5/8 = (1/2)² + 1/16`, and stop-loss expectation exactly
`1/8` at `d = 1/2`. -/
theorem interior_sharp :
    (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).mean (twoAtomClaim (1 / 4) (3 / 4)) = 1 / 2
    ∧ (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).secondMoment (twoAtomClaim (1 / 4) (3 / 4))
        = (1 / 2) ^ 2 + 1 / 16
    ∧ (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).stopLossExpectation (twoAtomClaim (1 / 4) (3 / 4)) (1 / 2)
        = 1 / 8 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FinLaw.mean, twoAtomLaw, twoAtomMass, twoAtomClaim]
    norm_num
  · simp [FinLaw.secondMoment, twoAtomLaw, twoAtomMass, twoAtomClaim]
    norm_num
  · simp only [FinLaw.stopLossExpectation, twoAtomLaw, twoAtomMass, twoAtomClaim,
      Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
    norm_num

end Research

-- Axiom audit.
#print axioms Research.interior_majorant
#print axioms Research.stopLoss_bound_interior
#print axioms Research.interior_sharp
