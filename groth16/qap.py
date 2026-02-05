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


###########################
# simple QAP for tesing two vectors are equal
###########################
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

###########################
# r1cs to QAP
# (L*a) * (R*a) = O*a
# L*a = [u1(x), u2(x),..., un(x)] * [a1, a2, ..., an] = a1*u1(x) + a2*u2(x) +...+ an*un(x) = u(x)
# R*a = v(x)
# O*a = w(x)
# balance poly degree:
# u(x)*v(x) = w(x) + h(x) * t(x), where t(x) = (x-1)*(x-2)...*(x-n)
###########################


"""
z = x^4 - 5*y^2*x^2
v1=x*x
v2=v1*v1 // x^4
v3=-5y*y
z=v2+v3*v1
"""

p = 79
Field = galois.GF(p)


def GF(v):
    return Field((v + p) % p)


# 1, z, x, y, v1, v2, v3
L = np.array(
    [
        [0, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, -5, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1],
    ]
)

L = GF(L)

R = np.array(
    [
        [0, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 1, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0],
    ]
)
R = GF(R)

O = np.array(
    [
        [0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 1],
        [0, 1, 0, 0, 0, -1, 0],
    ]
)
O = GF(O)

x = GF(4)
y = GF(-2)
v1 = x * x
v2 = v1 * v1  # x^4
v3 = -5 * y * y
z = v3 * v1 + v2  # -5y^2 * x^2

# # witness
a = np.array([1, z, x, y, v1, v2, v3])
a = GF(a)

assert all(np.equal(L.dot(a) * R.dot(a), O.dot(a))), "not equal"


def poly_col(col):
    xs = GF(np.arange(1, len(col) + 1, dtype=int))
    return galois.lagrange_poly(xs, col)


u_x_col = np.apply_along_axis(poly_col, 0, L)
print("len ux:", len(u_x_col))
print("check u3(x):", u_x_col[3])
v_x_col = np.apply_along_axis(poly_col, 0, R)
w_x_col = np.apply_along_axis(poly_col, 0, O)

t_x = (
    poly(GF(np.array([0, 1])), GF(np.array([-1, 0])))
    * poly(GF(np.array([0, 2])), GF(np.array([-2, 0])))
    * poly(GF(np.array([0, 3])), GF(np.array([-3, 0])))
    * poly(GF(np.array([0, 4])), GF(np.array([-4, 0])))
)
print("eval tx at 1,2,3,4:", t_x(1), t_x(2), t_x(3), t_x(4))


def inner_product_polynomials_with_witness(polys, witness):
    return sum((p * w for p, w in zip(polys, witness)), start=GF(0))


u_x = inner_product_polynomials_with_witness(u_x_col, a)
v_x = inner_product_polynomials_with_witness(v_x_col, a)
w_x = inner_product_polynomials_with_witness(w_x_col, a)

h_x = (u_x * v_x - w_x) // t_x
print("h(x):", h_x)
assert u_x * v_x == w_x + h_x * t_x
