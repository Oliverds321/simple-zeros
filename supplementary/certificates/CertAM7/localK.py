"""K-point local packing functional and the aggregated bound (stability route, simple zeros only).

F_K(g) = mu * sum_{i=1}^{K-1} g_i + sum_{s=1}^{K-1} beta_s sum_{i} w(g_i + ... + g_{i+s-1}),  beta_s = 2/(K-s),  w = k^2.
If F_K >= c for all g in [0,inf)^{K-1}, then for S simple on-line zeros in normalised length N(1+o(1)):
   tr Psi(M) >= (B/m) S - (B/A) tau N - o(N),  A = c (m-K+1),  B = Phi_m(A),  tau = mu (K-1)(m-K+1)/m,
and with S >= H N + tr Psi(M) - o(N):   S/N >= (H - (B/A) tau) / (1 - B/m).
"""
import numpy as np
from scipy.optimize import minimize


def cos_kernel(alpha):
    a = alpha / 2.0
    sa = np.sin(a) / a

    def k(x):
        y1 = np.pi * x - a
        y2 = np.pi * x + a
        return 0.5 * (np.sinc(y1 / np.pi) + np.sinc(y2 / np.pi)) / sa

    def kp(x):
        out = np.zeros_like(x)
        for sgn in (-1.0, 1.0):
            y = np.pi * x + sgn * a
            small = np.abs(y) < 1e-6
            yy = np.where(small, 1.0, y)
            d = np.where(small, -y / 3.0, (yy * np.cos(yy) - np.sin(yy)) / yy**2)
            out = out + d
        return 0.5 * np.pi * out / sa
    return k, kp


def span_matrix(K):
    rows, beta = [], []
    for s in range(1, K):
        for i in range(0, K - s):
            v = np.zeros(K - 1)
            v[i:i + s] = 1.0
            rows.append(v)
            beta.append(2.0 / (K - s))
    return np.array(rows), np.array(beta)


def make_F(k, kp, K, mu):
    V, beta = span_matrix(K)

    def F(g):
        g = np.abs(g)
        sp = V @ g
        kk = k(sp)
        kd = kp(sp)
        return mu * g.sum() + np.sum(beta * kk**2), mu + V.T @ (beta * 2 * kk * kd)
    return F, V, beta


def cmin(k, kp, K, mu, nstart=800, seed=0, zs=(1.06, 2.03)):
    F, V, beta = make_F(k, kp, K, mu)
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    n = K - 1
    for t in range(nstart):
        mode = t % 4
        if mode == 0:
            x = rng.uniform(0, 4, n)
        elif mode == 1:
            x = rng.choice([zs[0], zs[1], 1.0, 2.0], n) + rng.normal(0, 0.05, n)
        elif mode == 2:
            x = np.full(n, rng.uniform(0.7, 2.3)) + rng.normal(0, 0.03, n)
        else:
            x = rng.choice([0.0, zs[0], zs[1], 3.0, 1.5], n) + rng.normal(0, 0.1, n)
        r = minimize(F, np.abs(x), jac=True, method='L-BFGS-B', bounds=[(0, 400)] * n)
        if r.fun < best[0]:
            best = (r.fun, np.abs(r.x))
    return best


def Phi(E, m):
    return E if E <= m / (m - 1) else 2 * np.sqrt((m - 1) / m * E) - 1 + E / m


def aggregate(H, c, mu, K, mmax=4000):
    best = (-1, None)
    for m in range(K + 1, mmax):
        A = c * (m - K + 1)
        B = Phi(A, m)
        tau = mu * (K - 1) * (m - K + 1) / m
        p = (H - (B / A) * tau) / (1 - B / m)
        if p > best[0]:
            best = (p, m)
    return best
