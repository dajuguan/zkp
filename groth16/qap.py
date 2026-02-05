import galois
import numpy as np

p = 17
GF = galois.GF(p)

xs = GF(np.array([1, 2, 3]))
v1 = GF(np.array([1, 4, 9]))
v2 = GF(np.array([2, 12, 36]) % p)


def poly(xs, v):
    return galois.lagrange_poly(xs, v)


# f2 = poly(xs, v2)
# print(GF.properties)


A = GF(np.matrix([[6, 3], [4, 7]]))
B = GF(np.matrix([[3, 9], [12, 6]]))
v1 = GF(np.array([2, 4]))
v2 = GF(np.array([2, 2]))
# tesing A*v1 = B*v2 with O(n)
left = A.dot(v1)
right = B.dot(v2)
assert (left == right).all()

# testing A*v1 = B*v2 with O(1) at a random point by invoking the Schwartz-Zippel Lemma
x = GF(np.array([1, 2]))
poly_a1 = poly(x, A[:, 0])
poly_a2 = poly(x, A[:, 1])
poly_b1 = poly(x, B[:, 0])
poly_b2 = poly(x, B[:, 1])

poly_left = poly_a1 * v1[0] + poly_a2 * v1[1]
poly_right = poly_b1 * v2[0] + poly_b2 * v2[1]
print("left:", poly_left)
print("right", poly_right)
assert poly_left == poly_right

rho = np.random.randint(0, p)
tau = GF(rho)
assert poly_left(tau) == poly_right(tau)
