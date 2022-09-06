from z3 import *

def sqrt(n) :
    sqrtn = Real('sqrtn')
    s = Solver()
    s.add(True) # replace True with required declarative spec
    isSat = s.check()
    if (isSat) :
        return s.model()
    return -1
    
print(sqrt(9))