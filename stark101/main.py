from field import FieldElement as F

## ===========================Part 1=====================================##
# -------------------FibonacciSq Trace-------------------
a = [F(1), F(3141592)]
while len(a) < 1023:
    a.append(a[-2]**2 + a[-1]**2)

## check trace is correct
assert len(a) == 1023, 'The trace must consist of exactly 1023 elements.'
assert a[0] == F(1), 'The first element in the trace must be the unit element.'
for i in range(2, 1023):
    assert a[i] == a[i - 1] * a[i - 1] + a[i - 2] * a[i - 2], f'The FibonacciSq recursion rule does not apply for index {i}'
assert a[1022] == F(2338775057), 'Wrong last element!'
print('Trace Verifying Success!')

# -------------------Find a Group of Size 1024-------------------
g = F.generator() ** (3 * 2 ** 20)
G = [g ** i for i in range(1024)]

## Checks that g and G are correct.
assert g.is_order(1024), 'The generator g is of wrong order.'
b = F(1)
for i in range(1023):
    assert b == G[i], 'The i-th place in G is not equal to the i-th power of g.'
    b = b * g
    assert b != F(1), f'g is of order {i + 1}'
    
if b * g == F(1):
    print('Generator Verifying Success!')
else:
    print('g is of order > 1024')

# -------------------Interpolating a Polynomial-------------------
from polynomial import interpolate_poly
# check evaluation is correct
# a_poly = interpolate_poly(G[:-1], a)
# a_eval = a_poly.eval(2)
# assert a_eval == F(1302089273)
# print('Success!')


# -------------------Evaluate on coset-------------------
import pickle
import os
w = F.generator()
h = w ** ((2 ** 30 * 3) // 8192)
H = [h ** i for i in range(8192)]
eval_domain = [w * x for x in H]
f_file = "cache/f.obj"
if os.path.exists(f_file):
    file = open(f_file,'rb')
    f = pickle.load(file)
    file.close()
else:
    f = interpolate_poly(G[:-1], a)
    file = open(f_file,'wb')
    pickle.dump(f, file)
    file.close()
f_eval = [f(d) for d in eval_domain]

# Test against a precomputed hash.
from hashlib import sha256
from channel import serialize
assert '1d357f674c27194715d1440f6a166e30855550cb8cb8efeb72827f6a1bf9b5bb' == sha256(serialize(f_eval).encode()).hexdigest()
print('Coset Evaluation Success!')

# -------------------Commitment-------------------
from merkle import MerkleTree
f_merkle = MerkleTree(f_eval)
assert f_merkle.root == '6c266a104eeaceae93c14ad799ce595ec8c2764359d7ad1b4b7c57a4da52be04'
print('Merkle Root Check Success!')

# -------------------Transcripts-------------------
from channel import Channel
channel = Channel()
channel.send(f_merkle.root)

for v in [a, g, G, h, H, eval_domain, f, f_eval, f_merkle, channel]:
    assert v!=None

## ===========================Part 2=====================================##
from polynomial import interpolate_poly, X, prod
# The First Constraint:
numer0 = f - 1
denom0 = X-1
p0 = numer0 / denom0
assert p0(2718) == 2509888982
print('First Constrain Check Success!')

# The Second Constraint:
numer1 = f - 2338775057
denom1 = X - g**1022
p1 = numer1 / denom1
assert p1(5772) == 232961446
print('Second Constrain Check Success!')

# Other Constraints:
numer2 = f(g**2*X) - (f(g*X))**2 - f**2
denom2 = (X**1024 - 1)/(X-g**1021)/(X-g**1022)/(X-g**1023)
print("Numerator at g^1020 is", numer2(g**1020))
print("Numerator at g^1021 is", numer2(g**1021))
p2 = numer2 / denom2
assert p2.degree() == 1023, f'The degree of the third constraint is {p2.degree()} when it should be 1023.'
assert p2(31415) == 2090051528
print('Other Constraints Check Success!')

# Composition Polynomial
def get_CP(channel):
    alpha0 = channel.receive_random_field_element()
    alpha1 = channel.receive_random_field_element()
    alpha2 = channel.receive_random_field_element()
    return alpha0*p0 + alpha1*p1 + alpha2*p2

test_channel = Channel()
CP_test = get_CP(test_channel)
assert CP_test.degree() == 1023, f'The degree of cp is {CP_test.degree()} when it should be 1023.'
assert CP_test(2439804) == 838767343, f'cp(2439804) = {CP_test(2439804)}, when it should be 838767343'
print('Composition Polynomial Check Success!')

def CP_eval(channel):
    CP = get_CP(channel)
    return [CP(d) for d in eval_domain]

channel = Channel()
CP_merkle = MerkleTree(CP_eval(channel))
channel.send(CP_merkle.root)
assert CP_merkle.root == 'a8c87ef9764af3fa005a1a2cf3ec8db50e754ccb655be7597ead15ed4a9110f1', 'Merkle tree root is wrong.'
print('CP_merkle Check Success!')