from z3 import *

def sqrt(n):
    sqrtn = Real('sqrtn')
    s = Solver()
    # replace True with required declarative spec
<<<<<<< HEAD
    s.add(sqrtn**2 == n)
    s.add(sqrtn <= 0)
=======
    s.add(And(sqrtn**2 == n, sqrtn >= 0))
>>>>>>> bb666b94098a46ecf3a1800e72a117671208a012
    isSat = s.check()
    if (isSat == sat):
        return s.model()
    return -1


print(sqrt(17))
