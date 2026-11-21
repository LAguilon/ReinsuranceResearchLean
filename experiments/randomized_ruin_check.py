"""Stage A — stop-loss envelope bound for the ruin probability (Milestone 3).

Chain to test numerically:
  pi_X(d) = E[(X-d)+],  Fbar_I(y) = pi_X(y)/mu   (integrated tail, equal means)
  X <=_sl Y  <=>  X_I <=_st Y_I
  psi(u) = (1-rho) sum_n rho^n P(S_n > u),  S_n ~ F_I^{*n}   (Pollaczek-Khinchine)
  pi_sup(d) = sup over the class of E[(X-d)+]  = f(min(t,mu))  [our closed form]
  => psi_F(u) <= psi_G(u) for the law G with stop-loss transform pi_sup.

The test: random 3-atom laws with exact (mu, sigma^2), compare psi_F with psi_G.
"""
from math import sqrt
from random import Random

MU, S2, RHO, UMAX = 4.0, 4.0, 0.5, 12


def f(A, B, s):
    return (s * s * A + s * B) / (s * s + B)


def pi_sup(d, mu=MU, s2=S2):
    A = mu - d
    t = A + sqrt(A * A + s2)
    return max(0.0, f(A, s2, min(t, mu)))


def law_from_pi(mu, s2, U):
    """Recover the pmf of the law whose stop-loss transform is pi_sup."""
    pi = [pi_sup(k, mu, s2) for k in range(U + 3)]
    p = [0.0] * (U + 1)
    p[0] = 1.0 - pi[0] + pi[1]
    for k in range(1, U + 1):
        p[k] = pi[k - 1] - 2 * pi[k] + pi[k + 1]
    return p


def psi_pk(p, rho, U):
    """PK series psi(u) = (1-rho) sum_n rho^n P(S_n > u), truncated at U."""
    mu = sum(k * p[k] for k in range(len(p)))
    Fbar = [sum(p[k] for k in range(j + 1, len(p))) for j in range(len(p))]
    fI = [0.0] + [Fbar[k - 1] / mu for k in range(1, len(p))]
    # n-fold convolutions, truncated at U (CDF up to U is unaffected by mass above U)
    dist = [1.0] + [0.0] * U          # S_0 = 0
    psi = [0.0] * (U + 1)
    weight = 1.0
    for n in range(1, 60):
        new = [0.0] * (U + 1)
        for i, di in enumerate(dist):
            if di == 0.0:
                continue
            for k in range(1, len(fI)):
                if i + k > U:
                    break
                new[i + k] += di * fI[k]
        dist = new
        weight *= rho
        if weight < 1e-14:
            break
        # P(S_n > u) = 1 - P(S_n <= u)
        cdf = 0.0
        for u in range(U + 1):
            cdf += dist[u]
            psi[u] += (1 - rho) * weight * (1 - cdf)
    return psi


def random_law(rng, mu, s2, n_max=40):
    m2 = mu * mu + s2
    while True:
        a, b, c = sorted(rng.sample(range(0, n_max), 3))
        if not (a < b < c):
            continue
        den = (a - b) * (a - c)
        if den == 0:
            continue
        wa = (m2 - (b + c) * mu + b * c) / den
        wb = (m2 - (a + c) * mu + a * c) / ((b - a) * (b - c))
        wc = 1 - wa - wb
        if min(wa, wb, wc) < -1e-12:
            continue
        p = [0.0] * (n_max + 1)
        for x, w in ((a, wa), (b, wb), (c, wc)):
            p[x] += max(0.0, w)
        tot = sum(p)
        p = [v / tot for v in p]
        return p


if __name__ == "__main__":
    pG = law_from_pi(MU, S2, UMAX + 2)
    print("G pmf (first 10):", [round(v, 6) for v in pG[:10]], " sum=", round(sum(pG), 9))
    print("G mean:", round(sum(k * pG[k] for k in range(len(pG))), 6),
          " second moment:", round(sum(k * k * pG[k] for k in range(len(pG))), 6),
          " target:", MU, MU * MU + S2)
    psiG = psi_pk(pG, RHO, UMAX)
    print("psi_G:", [round(v, 6) for v in psiG])
    rng = Random(20261121)
    worst = 0.0
    maxpsi = [0.0] * (UMAX + 1)
    fails = 0
    for trial in range(200):
        p = random_law(rng, MU, S2)
        psi = psi_pk(p, RHO, UMAX)
        for u in range(UMAX + 1):
            maxpsi[u] = max(maxpsi[u], psi[u])
            worst = max(worst, psi[u] - psiG[u])
            if psi[u] > psiG[u] + 1e-9:
                fails += 1
    print("max over 200 random laws of (psi_F - psi_G):", round(worst, 9))
    print("violations:", fails)
    print("u        :", list(range(UMAX + 1)))
    print("sup_F psi:", [round(v, 6) for v in maxpsi])
    print("psi_G    :", [round(v, 6) for v in psiG])
    print("gap      :", [round(psiG[u] - maxpsi[u], 6) for u in range(UMAX + 1)])
