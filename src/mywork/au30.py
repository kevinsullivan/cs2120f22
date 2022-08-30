from z3 import *

# x + y + z == 100
# 15x + y + 0.25*z == 100
# x >= 1, y >= 1, z>= 1

x = Int('x')
y = Int('y')
z = Int('z')

s = Solver()
s.add(x + y + z == 100)
s.add(1500*x + 100*y + 25*z == 10000)
s.add(And(x >= 1, y >= 1, z>= 1))
print(s.check())
print(s.model())

