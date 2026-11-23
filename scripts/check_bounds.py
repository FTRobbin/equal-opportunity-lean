#!/usr/bin/env python3
"""Numeric cross-checks of the closed forms stated in EqualOpportunity/Paper.lean.

Not a proof: a cheap guard against stating something false before investing in a Lean proof.
Units: for the discrete distribution, noise is an integer bucket index in {0..k} and the
adversary's in-window offsets only matter through their relative order.  For the uniform
distribution, time is measured in units of Delta_noise, so alpha = Delta_net / Delta_noise.

Run:  python3 scripts/check_bounds.py
"""
import itertools
import random
from fractions import Fraction
from math import comb, factorial


def discrete_extremes(k: int, n: int):
    """Max and min over target orders pi of Pr[pi], adversary's offsets ranked 0 < 1 < ... < n-1.

    By symmetry this covers every assignment of distinct offsets.  Returns exact fractions.
    """
    total = (k + 1) ** n
    best, worst = Fraction(0), Fraction(1)
    for pi in itertools.permutations(range(n)):
        cnt = 0
        for s in itertools.product(range(k + 1), repeat=n):
            order = sorted(range(n), key=lambda i: (s[i], i))  # bucket first, then offset rank
            cnt += order == list(pi)
        pr = Fraction(cnt, total)
        best, worst = max(best, pr), min(worst, pr)
    return best, worst


def check_discrete():
    print("== Theorem 3.4 (discrete): Pr[pi] in [C(k+1,n), C(k+n,n)] / (k+1)^n")
    for k, n in [(0, 2), (1, 2), (2, 2), (1, 3), (2, 3), (3, 3), (2, 4), (1, 4)]:
        hi, lo = discrete_extremes(k, n)
        exp_hi = Fraction(comb(k + n, n), (k + 1) ** n)
        exp_lo = Fraction(comb(k + 1, n), (k + 1) ** n)
        ok = hi == exp_hi and lo == exp_lo
        print(f"  k={k} n={n}: max={hi} min={lo}  {'ok' if ok else 'MISMATCH'}")
        assert ok

    print("== Theorem 3.4 dominance: C(k+n,n) + C(k+1,n) >= 2 (k+1)^n / n!  for 0 <= k,n <= 120")
    bad = [(k, n) for k in range(121) for n in range(121)
           if factorial(n) * (comb(k + n, n) + comb(k + 1, n)) < 2 * (k + 1) ** n]
    print(f"  violations: {bad}")
    assert not bad


def mc(event, trials: int) -> float:
    return sum(event() for _ in range(trials)) / trials


def check_uniform(trials: int = 400_000):
    random.seed(1)
    u = random.random

    print("== Appendix Thm 3.3 (uniform, n=2): sup Pr[i1 < i2] = 1/2 + alpha - alpha^2/2")
    for a in (0.25, 0.5, 1.0):
        sim = mc(lambda: u() < a + u(), trials)  # offsets (0, alpha)
        print(f"  alpha={a}: sim={sim:.4f}  formula={0.5 + a - a * a / 2:.4f}")

    print("== Appendix Thm 3.4 lower (uniform): inf Pr[pi] = (1-alpha)^n / n!")
    for a, n in [(0.25, 3), (0.5, 3), (0.5, 4)]:
        # first command of pi gets offset alpha, last gets 0, the rest anything (here alpha/2)
        offs = [a] + [a / 2] * (n - 2) + [0.0]

        def ev():
            x = [o + u() for o in offs]
            return all(x[i] < x[i + 1] for i in range(n - 1))
        print(f"  alpha={a} n={n}: sim={mc(ev, trials):.4f}  formula={(1 - a) ** n / factorial(n):.4f}")

    print("== Appendix Thm 3.4 upper (uniform): ((1+alpha)^n - n alpha^n) / n!")
    print("   adaptive greedy attains it; the best non-adaptive assignment for n=3 does not")
    for a in (0.5, 1.0):
        n = 3
        paper = ((1 + a) ** n - n * a ** n) / factorial(n)

        def adaptive():
            t, prev = 0.0, -1.0
            for _ in range(n):
                x = t + u()
                if x <= prev:
                    return False
                prev, t = x, min(x, a)
            return True

        def nonadaptive(offs):
            x = [o + u() for o in offs]
            return x[0] < x[1] < x[2]

        grid = [i * a / 4 for i in range(5)]
        best = max((mc(lambda t=t: nonadaptive(t), 40_000), t)
                   for t in itertools.product(grid, repeat=3))
        conj = 1 / 6 + a / 2 + a * a / 4 - a ** 3 / 6
        print(f"  alpha={a}: paper={paper:.4f}  adaptive sim={mc(adaptive, trials):.4f}  "
              f"non-adaptive grid best={best[0]:.4f} at {best[1]}  conjectured={conj:.4f}")
        assert best[0] <= paper + 0.01


if __name__ == "__main__":
    check_discrete()
    check_uniform()
    print("all checks passed")
