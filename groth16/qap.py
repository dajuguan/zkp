import galois
import numpy as np

p = 17
GF = galois.GF(p)

xs = GF(np.array([1, 2, 3]))
v1 = GF(np.array([1, 4, 9]))
v2 = GF(np.array([2, 12, 36]) % p)


def poly(xs, v):
    return galois.lagrange_poly(xs, v)


f1 = poly(xs, v1)
print(f1)
