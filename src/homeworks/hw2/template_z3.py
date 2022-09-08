# Be sure you've done pip install z3-solver
from z3 import *


# Here's a file you can often copy as a starting 
# point on a working program to solve some problem
# of interest. Here the problem is to compute and
# return a non-negative square root of argument, n 
def sqrt(n):
    
    
    # Create z3 variable(s) representing the unknown
    # Here, the unknown, x, is the square root of n.
    x = Real('x')
    
    
    # Important: This is where you express what
    # values count as solutions using propositional
    # logic, but in the slightly different syntax
    # of Z3 expressions.
    C1 = (x*x == n)     # a solution squared must be n
    C2 = (x >= 0)       # and must also be non-negative
    C = And(C1, C2)     # combine using logical "and"
    
    
    # Create a Z3 "SMT" solver object, and give it 
    # the overall constraint to be solved, here C.
    s = Solver()
    s.add(C)
    
    # Run the Z3 model finder, capturing "sat"
    # or "unsat" as the return value 
    isSat = s.check()
    
    # If there's a model/solution return it 
    if (isSat == sat):
        return s.model()
    # otherwise return inconsistent value for error
    return -1

# Set up and run the function and report its results
n = 17
s = sqrt(n)
if (s == -1) :
    print("There is no real square root of", n)
else :
    print("The non-negative square root of", n, " is ", s)
