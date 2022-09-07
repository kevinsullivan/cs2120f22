from z3 import *

# x + y + z == 100
# 15x + y + 0.25*z == 100
# x >= 1, y >= 1, z>= 1

x = Real('x')
y = Real('y')
z = Real('z')

s = Solver()
s.add(3*x + 2*y - z == 1)
s.add(2*x + 2*y + 4*z == -2)
s.add(-2*x + y - 2*z == 0)
print(s.check())
print(s.model())

