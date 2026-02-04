import numpy as np

"""
-2+z = x * y
witness = [1,x,y,z]

"""

out = np.matrix([-2, 0, 0, 1])
left = np.matrix([0, 1, 0, 0])
right = np.matrix([0, 0, 1, 0])

x = np.random.randint(1, 1000)
y = np.random.randint(1, 1000)
z = x * y + 2
witness = np.array([1, x, y, z])

assert out.dot(witness) == left.dot(witness) * right.dot(witness)
