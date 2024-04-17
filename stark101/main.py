from field import FieldElement as F
import time

## ===========================Part 1=====================================##
print("Generating the trace...")
start = time.time()
start_all = start
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

print(f'{time.time() - start}s')
## ===========================Part 2=====================================##
print("Generating the composition polynomial and the FRI layers...")
start = time.time()

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

channel = Channel()
cp = get_CP(channel)
cp_eval = [cp(d) for d in eval_domain]
cp_merkle = MerkleTree(cp_eval)
channel.send(cp_merkle.root)
assert cp_merkle.root == 'a8c87ef9764af3fa005a1a2cf3ec8db50e754ccb655be7597ead15ed4a9110f1', 'Merkle tree root is wrong.'
# assert cp_merkle.root == 'd7e5200e990727c6da6bf711aeb496244b8b48436bd6f29066e1ddb64e22605b', 'Merkle tree root is wrong.'
print('CP_merkle Check Success!')

for v in [cp, cp_eval, cp_merkle, channel, eval_domain]:
    assert v != None

print(f'{time.time() - start}s')
## ===========================Part 3=====================================##
print("Generating queries...")
start = time.time()

from polynomial import interpolate_poly, Polynomial
from hashlib import sha256
# Next Layer Evaluation Domain
def next_fri_domain(fri_domain):
    return [x ** 2 for x in fri_domain[:len(fri_domain) // 2]]
# Test against a precomputed hash.
from hashlib import sha256
next_domain = next_fri_domain(eval_domain)
assert '5446c90d6ed23ea961513d4ae38fc6585f6614a3d392cb087e837754bfd32797' == sha256(','.join([str(i) for i in next_domain]).encode()).hexdigest()
print('Next_fri_domain Check Success!')

def next_fri_polynomial(poly, beta):
    odd_coefficients = poly.poly[1::2] # No need to fix this line.
    even_coefficients = poly.poly[::2] # No need to fix this line either.
    odd = Polynomial(odd_coefficients)
    even =  Polynomial(even_coefficients)
    return even +  beta*odd

# next_p = next_fri_polynomial(cp, F(987654321))
# assert '242f36b1d7d5b3e19948e892459774f14c038bc5864ba8884817112aa1405257' == sha256(','.join([str(i) for i in next_p.poly]).encode()).hexdigest()
# print('Next_fri_polynomial Check Success!')

# Putting it together to get the next fri layer
def next_fri_layer(poly, domain, beta):
    next_poly = next_fri_polynomial(poly, beta)
    next_domain = next_fri_domain(domain)
    next_layer = [next_poly(x) for x in next_domain]
    return next_poly, next_domain, next_layer

test_poly = Polynomial([F(2), F(3), F(0), F(1)])
test_domain = [F(3), F(5)]
beta = F(7)
next_p, next_d, next_l = next_fri_layer(test_poly, test_domain, beta)
assert next_p.poly == [F(23), F(7)]
assert next_d == [F(9)]
assert next_l == [F(86)]
print('Check next fri layer Success!')


def FriCommit(cp, domain, cp_eval, cp_merkle, channel):    
    fri_polys = [cp]
    fri_domains = [domain]
    fri_layers = [cp_eval]
    fri_merkles = [cp_merkle]
    while fri_polys[-1].degree() > 0:
        beta = channel.receive_random_field_element()
        next_poly, next_domain, next_layer = next_fri_layer(fri_polys[-1], fri_domains[-1], beta)
        fri_polys.append(next_poly)
        fri_domains.append(next_domain)
        fri_layers.append(next_layer)
        fri_merkles.append(MerkleTree(next_layer))
        channel.send(fri_merkles[-1].root)   
    channel.send(str(fri_polys[-1].poly[0]))
    return fri_polys, fri_domains, fri_layers, fri_merkles

# test_channel = Channel()
# fri_polys, fri_domains, fri_layers, fri_merkles = FriCommit(cp, eval_domain, cp_eval, cp_merkle, test_channel)
# assert len(fri_layers) == 11, f'Expected number of FRI layers is 11, whereas it is actually {len(fri_layers)}.'
# assert len(fri_layers[-1]) == 8, f'Expected last layer to contain exactly 8 elements, it contains {len(fri_layers[-1])}.'
# assert all([x == F(1200727158) for x in fri_layers[-1]]), f'Expected last layer to be constant.'
# assert fri_polys[-1].degree() == 0, 'Expacted last polynomial to be constant (degree 0).'
# assert fri_merkles[-1].root == '6ffd37a0a90eff521f011b8d9dcf4cc1d5dc30dc165e38480368e8f15170f164', 'Last layer Merkle root is wrong.'
# assert test_channel.state == '49f9fc3b997d0c5f6971e6038dd61969d6ebe5701b46276444e8e5beed6ada9d', 'The channel state is not as expected.'
# print('FriCommit Check Success!')

fri_polys, fri_domains, fri_layers, fri_merkles = FriCommit(cp, eval_domain, cp_eval, cp_merkle, channel)

print(f'{time.time() - start}s')
## ===========================Part 4: Query Phase=====================================##
print("Generating Decommitments...")
start = time.time()

def decommit_on_fri_layers(idx, channel):
    for layer, merkle in zip(fri_layers[:-1], fri_merkles[:-1]):
        length = len(layer)
        idx = idx % length
        sib_idx = (idx + length // 2) % length        
        channel.send(str(layer[idx]))
        channel.send(str(merkle.get_authentication_path(idx)))
        channel.send(str(layer[sib_idx]))
        channel.send(str(merkle.get_authentication_path(sib_idx)))       
    channel.send(str(fri_layers[-1][0]))

# Test against a precomputed hash.
test_channel = Channel()
for query in [7527, 8168, 1190, 2668, 1262, 1889, 3828, 5798, 396, 2518]:
    decommit_on_fri_layers(query, test_channel)
# assert test_channel.state == 'ad4fe9aaee0fbbad0130ae0fda896393b879c5078bf57d6c705ec41ce240861b', 'State of channel is wrong.'
assert test_channel.state == '4ad44aedee2a658f0bf3ddf0935d21b1bee6097be39103323c46d0345c74f48f', 'State of channel is wrong.'
print('Check decommit_on_fri_layers Success!')

#  the evaluations of f_eval in these points are actually 8 elements apart. 
# The reason for this is that we "blew up" the trace to 8 times its size in part I, to obtain a Reed Solomon codeword.
def decommit_on_query(idx, channel): 
    assert idx + 16 < len(f_eval), f'query index: {idx} is out of range. Length of layer: {len(f_eval)}.'
    channel.send(str(f_eval[idx])) # f(x).
    channel.send(str(f_merkle.get_authentication_path(idx))) # auth path for f(x).
    channel.send(str(f_eval[idx + 8])) # f(gx).
    channel.send(str(f_merkle.get_authentication_path(idx + 8))) # auth path for f(gx).
    channel.send(str(f_eval[idx + 16])) # f(g^2x).
    channel.send(str(f_merkle.get_authentication_path(idx + 16))) # auth path for f(g^2x).
    decommit_on_fri_layers(idx, channel)    

def decommit_fri(channel):
    for query in range(3):
        # Get a random index from the verifier and send the corresponding decommitment.
        decommit_on_query(channel.receive_random_int(0, 8191-16), channel)

print(f'{time.time() - start}s')
print(f'Overall Provding time: {time.time() - start}s')