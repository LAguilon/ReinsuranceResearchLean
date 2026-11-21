/-
# Verification harness

This module exists to be *checked*, not imported: it imports every public research
module, prints the axiom footprint of every exported theorem, and instantiates the
main theorem at concrete rational data so that its hypotheses are proved
simultaneously satisfiable (non-vacuity).

CI runs `lake env lean Research/Verify.lean` and fails unless every printed
footprint is exactly `[propext, Classical.choice, Quot.sound]`.
-/
import Research.Bernoulli
import Research.StopLoss
import Research.StopLossBounded

namespace Research

/-- **Non-vacuity witness.**  The hypotheses of `stopLoss_bound` are satisfiable:
`μ = 1`, `d = 1/2`, and the two-point law `{0, 2}` with mass `1/2` on each atom
has mean `1` and second moment `2 = 2μ²`.  The theorem then applies, so it is not
a vacuous implication. -/
theorem stopLoss_bound_nonvacuous :
    (twoPointLaw 1).stopLossExpectation (twoPointClaim 1) (1 / 2) ≤ 1 - (1 / 2) / 2 := by
  have h := twoPoint_attains (μ := 1) (d := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact stopLoss_bound (twoPointLaw 1) (twoPointClaim 1) (μ := 1) (d := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; cases i <;> norm_num [twoPointClaim])
    h.1 h.2.1

end Research

/-! ## Axiom audit of every exported theorem -/

#print axioms Research.Coupling.iff
#print axioms Research.Coupling.convex
#print axioms Research.Coupling.expCost_mono
#print axioms Research.Coupling.expCost_le_comonotone
#print axioms Research.Coupling.countermonotone_le_expCost
#print axioms Research.stopLoss_convex
#print axioms Research.stopLoss_majorant
#print axioms Research.stopLoss_bound
#print axioms Research.twoPoint_attains
#print axioms Research.stopLoss_bound_nonvacuous
#print axioms Research.interior_majorant
#print axioms Research.stopLoss_bound_interior
#print axioms Research.interior_sharp
#print axioms Research.atomZero_majorant
#print axioms Research.stopLoss_bound_atom_zero
#print axioms Research.atomZero_sharp
#print axioms Research.atomTop_majorant
#print axioms Research.stopLoss_bound_atom_top
#print axioms Research.atomTop_sharp
