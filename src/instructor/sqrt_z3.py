from z3 import *

# Given n, solve for and return x such that x^2 = n


def sqrt(n):
    x = Real('x')
    s = Solver()
    s.add(x**2 == n)        # constraint specification!
    s.check()
    return (s.model())


print(sqrt(9))
