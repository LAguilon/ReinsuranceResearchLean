"""Exhaustive rational verification of Depunc/Bernoulli.lean claims.

Two independent checks:
  (1) The formalized two-point statements, on an exact rational grid.
  (2) A numerical look at the three-point case, where the dependence set is a
      polytope rather than a segment.
Exact arithmetic everywhere; no floating point in (1).
"""
from fractions import Fraction as F
from itertools import product

def exp_cost(phi, p, q, t):
    m00, m10, m01, m11 = 1 - p - q + t, p - t, q - t, t
    return phi(0) * m00 + phi(1) * (m10 + m01) + phi(2) * m11

def feasible(p, q, t):
    return max(F(0), p + q - 1) <= t <= min(p, q)

grid = [F(k, 4) for k in range(5)]          # p, q in {0, 1/4, ..., 1}
phis = [lambda x: x,                        # identity (convex)
        lambda x: x * x,                    # quadratic
        lambda x: max(x - F(1, 2), F(0)),   # stop-loss, d = 1/2
        lambda x: max(x - F(3, 2), F(0))]   # stop-loss, d = 3/2

checked = 0
for p in grid:
    for q in grid:
        ts = [F(k, 8) for k in range(-8, 17)]     # includes infeasible points
        for phi in phis:
            second_diff = phi(2) - 2 * phi(1) + phi(0)
            assert second_diff >= 0, "convexity precondition violated"
            vals = [(t, exp_cost(phi, p, q, t)) for t in ts if feasible(p, q, t)]
            lo_t, lo_v = min(vals, key=lambda s: s[1])
            hi_t, hi_v = max(vals, key=lambda s: s[1])
            # affine in t  =>  extrema sit exactly at the interval endpoints
            lo_e, hi_e = max(F(0), p + q - 1), min(p, q)
            assert lo_v == exp_cost(phi, p, q, lo_e), (p, q, lo_v)
            assert hi_v == exp_cost(phi, p, q, hi_e), (p, q, hi_v)
            # monotone in t
            ordered = sorted(vals)
            assert all(a[1] <= b[1] for a, b in zip(ordered, ordered[1:]))
            checked += 1
print("two-point checks passed:", checked)

# ---------------- three-point case ----------------
def es(alpha, law):
    """Expected shortfall of a discrete law given as {value: mass}."""
    vals = sorted(law)
    cum, var = F(0), None
    for v in vals:
        cum += law[v]
        if cum >= alpha:
            var = v
            break
    tail = sum(m * (v - var) for v, m in law.items() if v > var)
    return var + tail / (1 - alpha)

def sum_law(joint, n=3):
    law = {}
    for i in range(n):
        for j in range(n):
            law[i + j] = law.get(i + j, F(0)) + joint[i][j]
    return {k: v for k, v in law.items() if v > 0}

m = F(1, 3)
comonotone = [[m if i == j else F(0) for j in range(3)] for i in range(3)]

for alpha in [F(1, 2), F(3, 4), F(9, 10)]:
    best = (None, None); worst = (None, None); count = 0
    for t11, t12, t21, t22 in product([F(k, 12) for k in range(5)], repeat=4):
        t13 = m - t11 - t12
        t23 = m - t21 - t22
        t31 = m - t11 - t21
        t32 = m - t12 - t22
        t33 = m - t31 - t32
        cells = [[t11, t12, t13], [t21, t22, t23], [t31, t32, t33]]
        if any(c < 0 for row in cells for c in row):
            continue
        if any(sum(row) != m for row in cells):
            continue
        if any(sum(cells[i][j] for i in range(3)) != m for j in range(3)):
            continue
        v = es(alpha, sum_law(cells))
        count += 1
        if best[1] is None or v > best[1]:
            best = (cells, v)
        if worst[1] is None or v < worst[1]:
            worst = (cells, v)
    como = es(alpha, sum_law(comonotone))
    print(f"alpha={alpha}: feasible samplings={count}  comonotone ES={como}  "
          f"max={best[1]}  min={worst[1]}  max-is-comonotone={best[1] == como}")
    print("   argmin coupling:", [[str(c) for c in row] for row in worst[0]])
