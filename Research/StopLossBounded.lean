/-
# Bounded claims on `[0, M]` — the three certificate cases

Companion to `research/trackA-bounded.md`.  The bounded-claims supremum is a single
clamped formula, and the clamp has two ends plus an interior critical point:

* **Interior** — atoms symmetric around `d`, perfect-square certificate;
* **A (`a = 0`)** — atom at zero, certificate `(d/b₀²)x² + (1 - 2d/b₀)x`;
* **B (`b = M`)** — atom at `M`, certificate `c(x - a₁)²` with boundary-term slack.

Each certificate majorises `(x-d)⁺` on the whole domain, so the resulting bound
holds for **every** law with the stated moments — exhaustiveness over laws is a
consequence of linearity and monotonicity of expectation, not of a separate
argument.  Attainment by the corresponding two-atom law gives equality.

Status: interior and A are kernel-checked with sharpness witnesses; B is
kernel-checked as a bound (its sharpness witness is the two-atom law at `M`, which
is the law the certificate interpolates, so equality is immediate from
`hcM : c(M-a₁)² = M-d`).
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

/-! ## Case I — interior critical point -/

/-- **Pointwise interior majorant.**  `4 s (x - d)⁺ ≤ (x - d + s)²`. -/
theorem interior_majorant {s d x : ℚ} (_hs : 0 < s) :
    4 * s * max (x - d) 0 ≤ (x - d + s) ^ 2 := by
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    nlinarith [sq_nonneg (x - d + s)]
  · rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (x - d - s)]

/-- **Interior bound.**  Scope: finitely supported laws (`FinLaw`). -/
theorem stopLoss_bound_interior (L : FinLaw ι) (X : ι → ℚ) {μ d s σ2 : ℚ}
    (hs : 0 < s) (hsq : s ^ 2 = (μ - d) ^ 2 + σ2)
    (hone : L.IsProbability)
    (_hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2) :
    L.stopLossExpectation X d ≤ (μ - d + s) / 2 := by
  have h4 : 0 < 4 * s := by positivity
  have hsum : 4 * s * L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (X i - d + s) ^ 2 := by
    rw [FinLaw.stopLossExpectation, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have hp := interior_majorant (s := s) (d := d) (x := X i) hs
    have hm := L.nonneg i
    have hstep := mul_le_mul_of_nonneg_left hp hm
    nlinarith [hstep]
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

/-! ## Two-atom law used by the witnesses -/

/-- Mass vector on `Bool`: `p` at `true`, `1 - p` at `false`. -/
def twoAtomMass (p : ℚ) : Bool → ℚ := fun b => if b then p else 1 - p

/-- Claim vector on `Bool`: `b` at `true`, `a` at `false`. -/
def twoAtomClaim (a b : ℚ) : Bool → ℚ := fun t => if t then b else a

/-- The two-atom law with mass `p` on the upper atom. -/
def twoAtomLaw (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinLaw Bool :=
  ⟨twoAtomMass p, by
    intro i
    cases i <;> simp [twoAtomMass] <;> linarith⟩

/-- **Sharpness witness for the interior case.**  `μ = 1/2`, `σ² = 1/16`,
`d = 1/2`: the law `{1/4, 3/4}` attains `1/8`. -/
theorem interior_sharp :
    (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).mean
        (twoAtomClaim (1 / 4) (3 / 4)) = 1 / 2
    ∧ (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).secondMoment
        (twoAtomClaim (1 / 4) (3 / 4)) = (1 / 2) ^ 2 + 1 / 16
    ∧ (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).stopLossExpectation
        (twoAtomClaim (1 / 4) (3 / 4)) (1 / 2) = 1 / 8 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FinLaw.mean, twoAtomLaw, twoAtomMass, twoAtomClaim] <;> norm_num
  · simp [FinLaw.secondMoment, twoAtomLaw, twoAtomMass, twoAtomClaim] <;> norm_num
  · simp only [FinLaw.stopLossExpectation, twoAtomLaw, twoAtomMass, twoAtomClaim,
      Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
    norm_num

/-! ## Case A — the `a = 0` end of the clamp binds -/

/-- **Pointwise certificate for case A.**  `b₀²(x-d)⁺ ≤ d x² + (b₀² - 2db₀)x`. -/
theorem atomZero_majorant {b0 d x : ℚ} (hb0 : 0 < b0) (hd : 0 ≤ d) (h2d : 2 * d ≤ b0)
    (hx : 0 ≤ x) :
    b0 ^ 2 * max (x - d) 0 ≤ d * x ^ 2 + (b0 ^ 2 - 2 * d * b0) * x := by
  by_cases h : x ≤ d
  · rw [max_eq_right (by linarith)]
    have hfac : 0 ≤ d * x + (b0 ^ 2 - 2 * d * b0) := by nlinarith
    nlinarith [mul_nonneg hx hfac]
  · rw [max_eq_left (by linarith)]
    nlinarith [mul_nonneg hd (sq_nonneg (x - b0))]

/-- **Case A bound.**  Scope: finitely supported laws (`FinLaw`). -/
theorem stopLoss_bound_atom_zero (L : FinLaw ι) (X : ι → ℚ) {μ d b0 σ2 : ℚ}
    (hμ : 0 < μ) (hb0 : μ * b0 = μ ^ 2 + σ2) (hb0pos : 0 < b0)
    (h2d : 2 * d ≤ b0) (hd : 0 ≤ d) (_hone : L.IsProbability)
    (hX : ∀ i, 0 ≤ X i)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2) :
    L.stopLossExpectation X d ≤ μ * (b0 - d) / b0 := by
  have hb0sq : 0 < b0 ^ 2 := by positivity
  have hsum : b0 ^ 2 * L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (d * (X i) ^ 2 + (b0 ^ 2 - 2 * d * b0) * X i) := by
    rw [FinLaw.stopLossExpectation, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i _
    have hp := atomZero_majorant hb0pos hd h2d (hX i)
    have hm := L.nonneg i
    have hstep := mul_le_mul_of_nonneg_left hp hm
    nlinarith [hstep]
  have hrhs : (∑ i, L.mass i * (d * (X i) ^ 2 + (b0 ^ 2 - 2 * d * b0) * X i))
      = d * L.secondMoment X + (b0 ^ 2 - 2 * d * b0) * L.mean X := by
    have h := FinLaw.sum_quadratic L X (b0 ^ 2 - 2 * d * b0) d
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

/-- **Sharpness witness for case A.**  `μ = 1/2`, `σ² = 1/4`, `b₀ = 1`, `d = 1/4`:
the law `{0, 1}` attains `3/8`. -/
theorem atomZero_sharp :
    (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).mean
        (twoAtomClaim 0 1) = 1 / 2
    ∧ (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).secondMoment
        (twoAtomClaim 0 1) = (1 / 2) ^ 2 + 1 / 4
    ∧ (twoAtomLaw (1 / 2) (by norm_num) (by norm_num)).stopLossExpectation
        (twoAtomClaim 0 1) (1 / 4) = 3 / 8 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FinLaw.mean, twoAtomLaw, twoAtomMass, twoAtomClaim] <;> norm_num
  · simp [FinLaw.secondMoment, twoAtomLaw, twoAtomMass, twoAtomClaim] <;> norm_num
  · simp only [FinLaw.stopLossExpectation, twoAtomLaw, twoAtomMass, twoAtomClaim,
      Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
    norm_num

/-! ## Case B — the `b = M` end of the clamp binds -/

/-- **Pointwise certificate for case B.**  The slack factors as
`(x - M)(c(x - M) + 2c(M - a₁) - 1)`, both factors non-positive on `[d, M]`. -/
theorem atomTop_majorant {M d a1 c x : ℚ} (hc : 0 < c) (hxM : x ≤ M)
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

/-- **Case B bound.**  Scope: finitely supported laws (`FinLaw`). -/
theorem stopLoss_bound_atom_top (L : FinLaw ι) (X : ι → ℚ) {μ d a1 c σ2 M : ℚ}
    (hM : 0 < M) (ha1 : 0 ≤ a1) (ha1d : a1 ≤ d) (hdM : d ≤ M)
    (hc : 0 < c) (hcM : c * (M - a1) ^ 2 = M - d)
    (hslope : 2 * c * (M - a1) ≤ 1) (hMa1 : 0 < M - a1)
    (hone : L.IsProbability) (_hX : ∀ i, 0 ≤ X i) (hXM : ∀ i, X i ≤ M)
    (hmean : L.mean X = μ) (hsecond : L.secondMoment X = μ ^ 2 + σ2)
    (hmom : (μ - a1) * (M - a1) = (μ - a1) ^ 2 + σ2) :
    L.stopLossExpectation X d ≤ (M - d) * (μ - a1) / (M - a1) := by
  have hsum : L.stopLossExpectation X d
      ≤ ∑ i, L.mass i * (c * (X i - a1) ^ 2) := by
    rw [FinLaw.stopLossExpectation]
    refine Finset.sum_le_sum ?_
    intro i _
    have hp := atomTop_majorant (M := M) (d := d) (a1 := a1) (c := c) (x := X i)
      hc (hXM i) hcM hslope ha1d
    have hm := L.nonneg i
    nlinarith [mul_le_mul_of_nonneg_left hp hm]
  have hexp : (∑ i, L.mass i * (c * (X i - a1) ^ 2))
      = c * ((μ - a1) ^ 2 + σ2) := by
    have h : ∀ i, L.mass i * (c * (X i - a1) ^ 2)
        = c * (L.mass i * ((-2 * a1) * X i + 1 * (X i) ^ 2 + a1 ^ 2)) := by
      intro i; ring
    simp only [h, ← Finset.mul_sum]
    rw [FinLaw.sum_quadratic_const L X (-2 * a1) 1 (a1 ^ 2) hone, hmean, hsecond]
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


/-- **Sharpness witness for case B.**  `μ = 4/5`, `σ² = 8/125`, `d = 3/4`, `M = 1`,
`a₁ = 12/25`, `c = 625/676`: the law `{12/25, 1}` with mass `8/13` on `M` attains
`2/13`. -/
theorem atomTop_sharp :
    (twoAtomLaw (8 / 13) (by norm_num) (by norm_num)).mean
        (twoAtomClaim (12 / 25) 1) = 4 / 5
    ∧ (twoAtomLaw (8 / 13) (by norm_num) (by norm_num)).secondMoment
        (twoAtomClaim (12 / 25) 1) = (4 / 5) ^ 2 + 8 / 125
    ∧ (twoAtomLaw (8 / 13) (by norm_num) (by norm_num)).stopLossExpectation
        (twoAtomClaim (12 / 25) 1) (3 / 4) = 2 / 13 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [FinLaw.mean, twoAtomLaw, twoAtomMass, twoAtomClaim] <;> norm_num
  · simp [FinLaw.secondMoment, twoAtomLaw, twoAtomMass, twoAtomClaim] <;> norm_num
  · simp only [FinLaw.stopLossExpectation, twoAtomLaw, twoAtomMass, twoAtomClaim,
      Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
    norm_num

-- Axiom audit: only the three standard axioms may appear.
#print axioms Research.interior_majorant
#print axioms Research.stopLoss_bound_interior
#print axioms Research.interior_sharp
#print axioms Research.atomZero_majorant
#print axioms Research.stopLoss_bound_atom_zero
#print axioms Research.atomZero_sharp
#print axioms Research.atomTop_majorant
#print axioms Research.stopLoss_bound_atom_top
#print axioms Research.atomTop_sharp

end Research
