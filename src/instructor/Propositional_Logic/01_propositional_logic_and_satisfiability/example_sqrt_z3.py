from z3 import *


def sqrt(n):
    sqrtn = Real('sqrtn')
    s = Solver()
    # replace True with required declarative spec
    s.add(sqrtn**2 == n)
    s.add(sqrtn <= 0)
    isSat = s.check()
    if (isSat == sat):
        return s.model()
    return -1


print(sqrt(17))
