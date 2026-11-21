"""Stage A — bounded-claims stop-loss problem on [0, M].

Primal:  sup E[(X-d)^+]  over laws on [0, M] with E[X] = mu, E[X^2] = m2.
Dual:    inf E[q(X)]     over quadratics q with q >= (x-d)^+ on [0, M].

Structure used here
-------------------
For a two-atom law {a, b} with a < b and the prescribed moments, the classical
identity

    (mu - a) (b - mu) = sigma^2                                        (2pt)

holds, so two-atom laws are parametrised by s := mu - a > 0, with

    b = mu + sigma^2 / s,      p_b = s^2 / (s^2 + sigma^2).

Maximising p_b (b - d) over the admissible s gives a one-dimensional problem with
derivative sign  B (B + 2As - s^2) / (s^2 + B)^2,  A = mu - d, B = sigma^2, so the
interior critical point is s* = A + sqrt(A^2 + B), i.e.

    a* = d - sqrt((mu-d)^2 + sigma^2),   b* = d + sqrt((mu-d)^2 + sigma^2),

the symmetric pair around the retention d.  Clamping s to [sigma^2/(M-mu), mu]
produces the four candidate regimes evaluated below.

This script (i) evaluates the four closed-form candidates, (ii) solves the primal
by exhaustive three-atom enumeration on a grid, and (iii) reports the duality gap
between the best closed-form candidate and the enumerated primal.  Float64
throughout; exact rationals are derived in research/trackA-bounded.md.
"""

from itertools import combinations
from math import sqrt

M = 1.0


# ---------------------------------------------------------------- primitives
def payoff(x, d):
    return max(x - d, 0.0)


def weights(x1, x2, x3, mu, m2):
    """Weights of the unique law on {x1,x2,x3} with the prescribed moments."""
    out = []
    for xi, xj, xk in ((x1, x2, x3), (x2, x1, x3), (x3, x1, x2)):
        out.append((m2 - (xj + xk) * mu + xj * xk) / ((xi - xj) * (xi - xk)))
    return out


def primal_grid(n=160, mu=0.5, var_frac=0.5, d=0.3):
    """Exhaustive three-atom primal on a grid of step M/n."""
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


# ------------------------------------------------------------ closed forms
def candidates(mu, sigma2, d):
    """The four closed-form candidates; returns (value, label, atoms, weights)."""
    out = []

    # R1: atom exactly at the kink d, second atom b = mu + sigma2/(mu-d) <= M.
    #     Then X >= d a.s. and the value is the trivial upper bound mu - d.
    if mu - d > 0 and sigma2 <= (mu - d) * (M - mu):
        b = mu + sigma2 / (mu - d)
        p = (mu - d) / (b - d)
        out.append((mu - d, "R1 kink", (d, b), (1 - p, p)))

    # R2: interior tangency pair symmetric around d.
    sb = sqrt((mu - d) ** 2 + sigma2)
    a, b = d - sb, d + sb
    if sb > 0 and a >= 0 and b <= M:
        p = (mu - a) / (b - a)
        out.append((p * (b - d), "R2 interior", (a, b), (1 - p, p)))

    # R3: a = 0 binds -> law {0, m2/mu}
    b0 = (mu * mu + sigma2) / mu
    if b0 <= M and b0 > 0 and b0 > d:
        p = mu / b0
        out.append((p * payoff(b0, d), "R3 a=0", (0.0, b0), (1 - p, p)))

    # R4: b = M binds -> law {a1, M}
    if M - mu > 0:
        a1 = (mu * M - (mu * mu + sigma2)) / (M - mu)
        if 0 <= a1 < M:
            q = (mu - a1) / (M - a1)
            out.append((q * (M - d), "R4 b=M", (a1, M), (1 - q, q)))
    return out


def dual_certificate(atoms, d):
    """Quadratic interpolating the payoff at two atoms and tangent at the lower one.

    For a two-atom contact {a, b} with a < d < b the extremal certificate is
    q(x) = (x-a)^2 / (4 sqrt((mu-d)^2+sigma^2)); we reconstruct it by matching
    q(a) = 0, q'(a) = 0, q(b) = b - d and report the maximum violation of
    q >= (x-d)^+ on [0, M].
    """
    a, b = atoms
    if not (a < d < b):
        return None
    c = (b - d) / (b - a) ** 2
    # tangency at b requires q'(b) = 1; report whether that holds
    tangent = abs(2 * c * (b - a) - 1.0) < 1e-9
    worst = 0.0
    for i in range(4001):
        x = M * i / 4000
        worst = min(worst, c * (x - a) ** 2 - payoff(x, d))
    return c, tangent, worst


def main():
    print(f"{'mu':>5} {'var/max':>7} {'d':>4} {'closed':>9} {'primal':>9} {'gap':>9}  regime / atoms")
    worst = 0.0
    for mu in (0.2, 0.35, 0.5, 0.65, 0.8):
        for frac in (0.1, 0.4, 0.7, 0.95):
            for d in (0.0, 0.15, 0.3, 0.45, 0.6, 0.75, 0.9):
                sigma2 = frac * mu * (M - mu)
                cand = candidates(mu, sigma2, d)
                best_closed = max(cand, key=lambda t: t[0])
                (lp, atoms, p), m2 = primal_grid(mu=mu, var_frac=frac, d=d)
                gap = best_closed[0] - lp
                worst = min(worst, gap)
                sup = " ".join(f"{x:.3f}" for x in best_closed[2])
                print(f"{mu:5.2f} {frac:7.2f} {d:4.2f} {best_closed[0]:9.6f} {lp:9.6f} {gap:9.2e}  "
                      f"{best_closed[1]:12s} {sup}")
    print(f"\nworst (closed - primal) over all rows: {worst:.2e}   "
          "(>= 0 means the closed form is at least as large as the enumerated primal)")

# ---------------------------------------------------------- adversarial gate
def adversarial():
    """Boundary limits that must not break the closed form (AGENTS.md rule)."""
    checks = []
    for mu in (0.1, 0.5, 0.9):
        # zero variance: the law is degenerate at mu
        for d in (0.0, mu, M):
            cand = candidates(mu, 0.0, d)
            best = max(cand, key=lambda t: t[0])[0]
            checks.append((f"sigma2=0 mu={mu} d={d:.2f}", best, max(mu - d, 0.0),
                           abs(best - max(mu - d, 0.0)) < 1e-12))
        # maximal variance: the two-point law {0, M}
        s2max = mu * (M - mu)
        for d in (0.0, 0.5 * mu, mu, 0.5 * (mu + M)):
            cand = candidates(mu, s2max, d)
            best = max(cand, key=lambda t: t[0])[0]
            exact = mu * max(M - d, 0.0) / M     # law {0,M} puts mass mu/M on M
            checks.append((f"sigma2=max mu={mu} d={d:.2f}", best, exact,
                           abs(best - exact) < 1e-12))
        # d = 0 and d = M are the trivial ends
        checks.append((f"d=0 mu={mu}", max(candidates(mu, 0.25 * mu * (M - mu), 0.0),
                                           key=lambda t: t[0])[0], mu, None))
        checks.append((f"d=M mu={mu}", max(candidates(mu, 0.25 * mu * (M - mu), M),
                                           key=lambda t: t[0])[0], 0.0, None))
    ok = True
    for name, got, want, flag in checks:
        if flag is None:
            flag = abs(got - want) < 1e-12
        ok &= flag
        print(f"  {name:28s} closed={got:.9f} expected={want:.9f} {'PASS' if flag else 'FAIL'}")
    print("adversarial gate:", "PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    import sys
    if "--adversarial" in sys.argv:
        raise SystemExit(0 if adversarial() else 1)
    main()
