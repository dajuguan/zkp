from field import FieldElement as F

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
w = F.generator()
h = w ** ((2 ** 30 * 3) // 8192)
H = [h ** i for i in range(8192)]
eval_domain = [w * x for x in H]
f = interpolate_poly(G[:-1], a)
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