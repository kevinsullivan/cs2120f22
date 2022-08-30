
# Name: Hsi En Lai
# email: qzz5jq@virginia.edu

from z3 import *
from itertools import combinations

def at_most_one(literals):
    c = []
    for pair in combinations(literals, 2):
        a, b = pair[0], pair[1]
        c += [Or([Not(a), Not(b)])]
    return And(c)

x = [[Bool(f'x_{i}_{j}') for j in range(5)] for i in range(5)]

s = Solver()

for i in range(5):
    s.add(Or(x[i]))

for i in range(5):
    col = []
    for j in range(5):
        col += [x[j][i]]
    s.add(at_most_one(col))
    s.add(at_most_one(x[i]))

for i in range(4):
    dia_1 = []
    dia_2 = []
    dia_3 = []
    dia_4 = []

    for j in range(5 - i):
        dia_1 += [x[i + j][j]]
        dia_2 += [x[i + j][4 - j]]
        dia_3 += [x[4 - (i + j)][j]]
        dia_4 += [x[4 - (i + j)][4 - j]]

    s.add(at_most_one(dia_1))
    s.add(at_most_one(dia_2))
    s.add(at_most_one(dia_3))
    s.add(at_most_one(dia_4))

print(s.check())
m = s.model()

for i in range(5):
    line = ''
    for j in range(5):
        if m.evaluate(x[i][j]):
            line += 'x '
        else:
            line += '. '
    print(line)




# x = Bool('x')
# y = Bool('y')
# z = Bool('z')

# f1 = Or([x, y, z])
# f2 = Or([Not(x), Not(y)])
# f3 = Or([Not(y), Not(z)])

# F = And([f1, f2, f3])

# s = Solver()
# s.add(F)
# print(s.check())
# m = s.model()
# print(m)
# print(m.evaluate(x))
# print(m.evaluate(y))
# print(m.evaluate(z))