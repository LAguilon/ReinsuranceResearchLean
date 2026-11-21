"""Stage A — general-σ² unbounded stop-loss bound on [0, ∞).

Formula: sup E[(X-d)^+] = f(min(t, mu)) with
    A = mu - d,  t = A + sqrt(A^2 + sigma^2),
    f(s) = (s^2 A + s sigma^2) / (s^2 + sigma^2).

Independent check: enumerate three-atom laws on a truncated support [0, M] with
M large; the bounded supremum must approach the formula from below as M grows,
because [0, M] ⊂ [0, ∞).
"""
from itertools import combinations
from math import sqrt


def f(A, B, s):
    return (s * s * A + s * B) / (s * s + B)


def formula(mu, sigma2, d):
    A = mu - d
    t = A + sqrt(A * A + sigma2)
    return f(A, sigma2, min(t, mu))


def bounded_lp(M, mu, sigma2, d, step=None):
    # constant grid step, so growing M refines the domain rather than coarsening it
    if step is None:
        step = 5 * mu / 40
    n = max(30, int(round(M / step)))
    m2 = mu * mu + sigma2
    grid = [M * i / n for i in range(n + 1)]
    best = -1.0
    for x1, x2, x3 in combinations(grid, 3):
        p = []
        for xi, xj, xk in ((x1, x2, x3), (x2, x1, x3), (x3, x1, x2)):
            p.append((m2 - (xj + xk) * mu + xj * xk) / ((xi - xj) * (xi - xk)))
        if min(p) < -1e-12:
            continue
        val = p[0] * max(x1 - d, 0) + p[1] * max(x2 - d, 0) + p[2] * max(x3 - d, 0)
        best = max(best, val)
    return best


if __name__ == "__main__":
    print(f"{'mu':>5} {'sigma2':>7} {'d':>5} {'formula':>10} {'M=5mu':>10} {'M=20mu':>10}  monotone?")
    ok = True
    for mu in (0.5, 1.0):
        for s2 in (0.05, 0.5):
            for d in (0.0, 0.5 * mu, mu, 1.5 * mu):
                v = formula(mu, s2, d)
                step = 5 * mu / 40
                lo5 = bounded_lp(5 * mu, mu, s2, d, step)
                lo20 = bounded_lp(20 * mu, mu, s2, d, step)
                mono = lo5 <= v + 1e-9 and lo20 <= v + 1e-9 and lo5 <= lo20 + 1e-9
                ok &= mono
                print(f"{mu:5.2f} {s2:7.3f} {d:5.2f} {v:10.6f} {lo5:10.6f} {lo20:10.6f}  {mono}")
    print("truncation gate:", "PASS" if ok else "FAIL")
