"""Stage A — bounded-claims stop-loss problem on [0, M]  (corrected).

Primal:  sup E[(X-d)^+]  over laws on [0, M] with E[X] = mu, E[X^2] = m2.
Dual:    inf E[q(X)]     over quadratics q with q >= (x-d)^+ on [0, M].

Correction (2026-11-21): an earlier version of this script listed a "kink regime"
whose value was `mu - d`.  That is wrong: `(x-d)^+ >= x - d` pointwise, so `mu - d`
is a **lower** bound (Jensen), not a supremum.  The correct object is the single
clamped formula below; see research/trackA-bounded.md §3.

Reduction
---------
Two-atom laws with the prescribed moments satisfy (mu - a)(b - mu) = sigma^2, so
they are parametrised by s := mu - a in (0, mu], with

    b = mu + sigma^2/s,     p_b = s^2/(s^2 + sigma^2),

and the objective (for a <= d <= b) is

    f(s) = (s^2 (mu - d) + s sigma^2) / (s^2 + sigma^2).

f'(s) has the sign of sigma^2 (sigma^2 + 2(mu-d)s - s^2), so f increases up to

    s* = (mu - d) + sqrt((mu-d)^2 + sigma^2)

and decreases afterwards.  The admissible range is [sigma^2/(M-mu), mu] (the lower
end is b <= M, the upper end is a >= 0), hence

    sup = f( clamp(s*, sigma^2/(M-mu), mu) ).

Note s* > mu - d strictly whenever sigma^2 > 0, which is exactly why the Jensen
value mu - d is never the supremum except in the degenerate case sigma^2 = 0.

Float64 throughout; exact rationals are derived in research/trackA-bounded.md.
"""

from itertools import combinations
from math import sqrt

M = 1.0


def payoff(x, d):
    return max(x - d, 0.0)


def weights(x1, x2, x3, mu, m2):
    out = []
    for xi, xj, xk in ((x1, x2, x3), (x2, x1, x3), (x3, x1, x2)):
        out.append((m2 - (xj + xk) * mu + xj * xk) / ((xi - xj) * (xi - xk)))
    return out


def primal_grid(n=160, mu=0.5, var_frac=0.5, d=0.3):
    m2 = mu * mu + var_frac * mu * (M - mu)
    grid = [M * i / n for i in range(n + 1)]
    best = (-1.0, None, None)
    for x1, x2, x3 in combinations(grid, 3):
        p = weights(x1, x2, x3, mu, m2)
        if min(p) < -1e-12:
            continue
        val = p[0] * payoff(x1, d) + p[1] * payoff(x2, d) + p[2] * payoff(x3, d)
        if val > best[0]:
            best = (val, (x1, x2, x3), p)
    return best, m2


def supremum(mu, sigma2, d):
    """Closed form: (value, s, regime)."""
    if sigma2 <= 0.0:
        return max(mu - d, 0.0), 0.0, "degenerate"
    A, B = mu - d, sigma2
    s_star = A + sqrt(A * A + B)
    s_lo = B / (M - mu)
    s = min(max(s_star, s_lo), mu)
    val = (s * s * A + s * B) / (s * s + B)
    if s_star <= s_lo:
        regime = "b=M"
    elif s_star >= mu:
        regime = "a=0"
    else:
        regime = "interior"
    return max(val, 0.0), s, regime


def law_at(s, mu, sigma2, d):
    a = mu - s
    b = mu + sigma2 / s
    p = s * s / (s * s + sigma2)
    return a, b, p


def main():
    print(f"{'mu':>5} {'var/max':>7} {'d':>4} {'closed':>9} {'primal':>9} {'gap':>9}  regime  atoms")
    worst = 1e9
    for mu in (0.2, 0.35, 0.5, 0.65, 0.8):
        for frac in (0.1, 0.4, 0.7, 0.95):
            for d in (0.0, 0.15, 0.3, 0.45, 0.6, 0.75, 0.9):
                sigma2 = frac * mu * (M - mu)
                val, s, regime = supremum(mu, sigma2, d)
                (lp, atoms, p), m2 = primal_grid(mu=mu, var_frac=frac, d=d)
                gap = val - lp
                worst = min(worst, gap)
                a, b, pb = law_at(s, mu, sigma2, d) if s > 0 else (mu, mu, 1.0)
                print(f"{mu:5.2f} {frac:7.2f} {d:4.2f} {val:9.6f} {lp:9.6f} {gap:9.2e}  "
                      f"{regime:10s} ({a:.3f},{b:.3f})")
    print(f"\nworst (closed - primal): {worst:.2e}   "
          "(negative beyond grid error would mean the closed form is too small)")


def adversarial():
    ok = True
    def check(name, got, want, tol=1e-12):
        nonlocal ok
        good = abs(got - want) < tol
        ok &= good
        print(f"  {name:34s} closed={got:.9f} expected={want:.9f} {'PASS' if good else 'FAIL'}")

    for mu in (0.1, 0.5, 0.9):
        # zero variance: deterministic at mu
        for d in (0.0, mu, M):
            check(f"sigma2=0 mu={mu} d={d:.2f}", supremum(mu, 0.0, d)[0], max(mu - d, 0.0))
        # maximal variance: two-point law {0, M}
        s2max = mu * (M - mu)
        for d in (0.0, 0.5 * mu, mu, 0.5 * (mu + M)):
            check(f"sigma2=max mu={mu} d={d:.2f}", supremum(mu, s2max, d)[0],
                  mu * max(M - d, 0.0) / M)
        # trivial ends
        check(f"d=0 mu={mu}", supremum(mu, 0.25 * mu * (M - mu), 0.0)[0], mu)
        check(f"d=M mu={mu}", supremum(mu, 0.25 * mu * (M - mu), M)[0], 0.0)
    print("adversarial gate:", "PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    import sys
    if "--adversarial" in sys.argv:
        raise SystemExit(0 if adversarial() else 1)
    main()
