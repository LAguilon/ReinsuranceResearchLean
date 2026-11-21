# LITERATURE AUDIT — dependence uncertainty & extremal reinsurance

Audit date: **2026-11-21**. Method: Crossref REST API queries + reconstruction of
statements from titles/abstracts. **No keyword search engine was available in the
research environment**, so this is a *partial* audit: it certifies that the cited
papers exist, with the stated metadata, and that the finite two-point results in
this repository are classical. It does **not** certify that nothing newer exists.
Consequently no item is labelled `OPEN` unless the cited literature itself leaves
it open.

## Status labels

| Label | Meaning |
|---|---|
| `ESTABLISHED` | Published theorem, statement reconstructed from the source metadata/abstract |
| `REPRODUCED` | Our own kernel-checked derivation of a classical fact |
| `PARTIAL` | Literature solves a special case or an asymptotic version |
| `OPEN_CANDIDATE` | No solution found in this audit; likely open, not certified |
| `STATUS_UNCERTAIN` | Could not be settled with the access available |

## Track B — dependence uncertainty

| Reference | DOI | Contribution | Status here |
|---|---|---|---|
| Embrechts, Puccetti (2006), *Bounds for functions of dependent risks*, Finance & Stochastics 10 | 10.1007/s00780-006-0005-5 | Worst/best-case bounds for aggregate functions with fixed marginals | `ESTABLISHED` |
| Embrechts, Puccetti, Rüschendorf (2013), *Model uncertainty and VaR aggregation*, J. Banking & Finance 37 | 10.1016/j.jbankfin.2013.03.014 | Dual bounds for worst-case VaR; LP-based numerical bounds | `ESTABLISHED` |
| Puccetti, Wang, Wang (2013), *Complete mixability and asymptotic equivalence of worst-possible VaR and ES estimates*, Insurance: Math. & Econ. 53 | 10.1016/j.insmatheco.2013.09.017 | Worst-case VaR ≈ worst-case ES asymptotically in the number of risks for mixable marginals | `ESTABLISHED` |
| Bernard, Jiang, Wang (2014), *Risk aggregation with dependence uncertainty*, Insurance: Math. & Econ. 54 | 10.1016/j.insmatheco.2013.11.005 | Bounds on aggregate distributions under partial dependence information | `ESTABLISHED` |
| Wang, Wang (2016), *Joint mixability*, Math. of Operations Research 41 | 10.1287/moor.2015.0755 | Characterisation of joint/complete mixability; exact worst-case asymptotics | `ESTABLISHED` |
| Fadina, Hu, Liu, Xia (2025), *Optimal reinsurance with multivariate risks and dependence uncertainty*, EJOR 321, 231–242 | 10.1016/j.ejor.2024.09.037 | Optimal reinsurance under dependence uncertainty for multivariate risks | `ESTABLISHED` |
| Bernard, Rüschendorf, Vanduffel, *Value-at-Risk bounds with variance constraints* (SSRN working paper) | 10.2139/ssrn.2342068 | VaR bounds under moment (variance) constraints — bridge to Track A | `PARTIAL` (journal version not confirmed in this audit) |

**Finite two-point case.** The union-bound argument giving
`VaR_α(X+Y) ≤ VaR_α(X) + VaR_α(Y)` and the comonotone attainment are textbook
material that follows from the sources above; the kernel-checked development in
`Research/Bernoulli.lean` is therefore classified **`REPRODUCED`**, not new.

## Track A — ruin theory / Schmitter problem (deferred to a later stage)

| Reference | DOI | Contribution | Status here |
|---|---|---|---|
| Brockett, Goovaerts, Taylor (1991), *The Schmitter Problem*, ASTIN Bulletin 21(1) | 10.2143/ast.21.1.2005405 | Poses the extremal ruin-probability problem under moment constraints | `ESTABLISHED` |
| Kaas (1991), *The Schmitter Problem and a Related Problem: A Partial Solution*, ASTIN Bulletin 21(1) | 10.2143/ast.21.1.2005406 | Partial solution: extremal two-point/three-point structures | `ESTABLISHED` |
| Albrecher, Araujo-Acuña (2021), *On the Randomized Schmitter Problem*, MCAP | 10.1007/s11009-021-09910-5 | Randomised initial surplus; convex-order reformulation | `ESTABLISHED` |

**Correction to the mission brief.** "The Schmitter Problem and a Related Problem:
A Partial Solution" (1991) is **Kaas's** paper; Brockett–Goovaerts–Taylor (1991) is
titled *The Schmitter Problem*. The brief merges the two. Crossref lists both under
ASTIN Bulletin 21(1), 1991.

## Gap statement

Sharp finite-*n* worst-case **lower** bounds for ES under fixed marginals remain the
hard half of Track B: upper bounds follow from subadditivity and comonotone
attainment, and asymptotic results are known for mixable marginals, but exact
finite-`n` values are available only for special families. With the access available
here this is recorded as `OPEN_CANDIDATE` for general marginals, **not** as a
certified open problem.

## Track A — bounded support and moment-constrained stop-loss bounds

Audit date 2026-11-21, Crossref metadata. These are the classical sources behind
the bounded-claims problem (Issue #4); the results in this repository are
`REPRODUCED`, never novel.

| Reference | DOI | Contribution |
|---|---|---|
| Taylor (1977), *Upper bounds on stop-loss premiums under constraints on claim size distribution*, Scand. Actuar. J. 1977, 94–105 | 10.1080/03461238.1977.10405631 | Early moment-constrained stop-loss bounds |
| Goovaerts, De Vylder (1980), *Upper bounds on stop-loss premiums under constraints on claim size distributions as derived from representation theorems for distribution functions*, Scand. Actuar. J. 1980, 141–148 | 10.1080/03461238.1980.10408649 | Representation-theorem route to sharp bounds |
| De Vylder, Goovaerts, De Pril (1982), *Bounds on modified stop-loss premiums in case of known mean and variance of the risk variable*, ASTIN Bulletin 13, 23–36 | 10.1017/s0515036100006917 | Mean/variance stop-loss bounds — the direct ancestor of `Research/StopLoss.lean` |
| Jansen, Haezendonck, Goovaerts (1986), *Upper bounds on stop-loss premiums in case of known moments up to the fourth order*, Insurance Math. Econ. 5, 315–334 | 10.1016/0167-6687(86)90027-2 | Moment hierarchy; explains why three atoms suffice |
| Broeckx, Goovaerts, De Vylder (1986), *Ordering of risks and ruin probabilities*, Insurance Math. Econ. 5, 35–39 | 10.1016/0167-6687(86)90005-3 | Stop-loss order and ruin probabilities — the propagation step |
| Kaas, van Heerwaarden, Goovaerts (1988), *On stop-loss premiums for the individual model*, ASTIN Bulletin 18, 91–97 | 10.2143/ast.18.1.2014963 | Bounded-support extremal distributions |
| Heijnen (1990), *Best upper and lower bounds on modified stop-loss premiums in case of known range, mode, mean and variance*, Insurance Math. Econ. 9, 207–220 | 10.1016/0167-6687(90)90035-c | Bounded range plus moments — closest to Issue #4 |
| Kaas, van Heerwaarden (1992), *Stop-loss order, unequal means, and more dangerous distributions*, Insurance Math. Econ. 11, 71–77 | 10.1016/0167-6687(92)90089-t | Ordering with unequal means |
| Genest, Marceau, Mesfioui (2002), *Upper stop-loss bounds for sums of possibly dependent risks with given means and variances*, Statist. Probab. Lett. 57, 33–41 | 10.1016/s0167-7152(02)00039-1 | Multivariate mean/variance bounds |

**Unverified citation.** Hürlimann (1998) is named in the task brief but did not
resolve to a unique record in this audit; it is therefore **not** cited here until
a DOI is confirmed. Absence from this table means "not verified", not "not
relevant".
