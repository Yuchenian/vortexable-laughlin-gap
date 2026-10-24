"""Separate standard-library exact-arithmetic re-evaluation of the paper's bounds."""
from fractions import Fraction as F
from math import factorial

def gap(alpha, kappa):
    d = 2 * alpha / (1 + alpha)
    return kappa / (1 - alpha)**2 * (F(1, 5) - 14*d - d*d)

def exp_lower(x, order=24):
    return sum((x**j / factorial(j) for j in range(order + 1)), F(0))

assert exp_lower(F(157, 100)) > F(100, 21)
assert exp_lower(F(157, 50)) > 23
assert exp_lower(F(157, 25)) > 500
assert 14**2 > 8**2 * 3

alpha_nodal = 2*F(1, 500) + F(1, 500)**2
kappa_nodal = F(9, 2) - (F(3, 2) + F(2, 23) + F(1, 2*23**4))**2
assert alpha_nodal == F(1001, 250000)
assert kappa_nodal == F(310356353097, 156621970562)
cases = [
    ('first harmonic', F(21, 10000), F(99, 100)**2, F(11493880722000, 82643899175161)),
    ('second harmonic', F(1, 1000), F(1, 4), F(1164650000, 27026972973)),
    ('sphere', F(1, 1000), F(999, 1000)**2, F(861841, 5010005)),
    ('nodal', alpha_nodal, kappa_nodal, F(5992934159531101049706250000000, 33988053096870625665692548678809)),
]
for name, alpha, kappa, expected in cases:
    result = gap(alpha, kappa)
    assert result == expected and result > 0
    print(f'{name}: {result} = {float(result):.16f}')
assert gap(alpha_nodal, kappa_nodal) > F(1763, 10000)
gamma = F(1401624220840445441298243497, 6400000000000000000000000000)
assert gamma > F(1, 5)
print('PASS: exact rational bounds, finite Taylor estimates, and reference-gap comparison.')
