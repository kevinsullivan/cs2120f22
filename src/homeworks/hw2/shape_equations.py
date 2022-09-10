# Be sure you've done pip install z3-solver
from z3 import *


def shapeq():
    
    # Express what properties a solution must
    # have by logical propositions involving
    # relevant variables in the problem domain 
    # understood as constraints on an acceptable
    # solution. 
    
    # Start by asking "What are the unknowns."
    # Create a Z3 variable to represent each
    # such value. In the problem at hand, the
    # unknowns are numbers corresponding to 
    # the shapes that make the equations all
    # true at once (so the overall And is also
    # true). 
    tri, sq, cir = Reals('t s o') # note: plural
    
    
    # Using the Z3 library for Python, we can
    # assign propositional logic propositions,
    # a.k.a. constraints to variables, as we do
    # here, to the variables C1, C2, and C3. 
    #
    # We then define the overall constraint to
    # be satisfied as the conjunction (and) of 
    # the propositions we've called C1, C2, C3.
    C1 = (tri + sq + cir == 10)  # tri + sq + cir = 10
    C2 = (cir + sq - tri == 6)   # cir + sq - tri = 6
    C3 = (cir + tri - sq == 4)   # cir + tri - sq = 4
    C = And(C1, C2, C3)     # now conjoin them
    # C effectively specifies a set of (zero or 
    # more) interpretations, each one assigning
    # a real value to tri, sq, and cir in such a
    # was as to satisfy the overall conjunction
    # of the three smaller constraints, above. 
    
    # Create a Z3 "SMT" solver object, and give it 
    # the overall constraint to be solved: here C.
    sq = Solver()
    sq.add(C)
    
    # Run the Z3 model checker, capturing either
    # "sat" or "unsat" as the return value, with
    # a model, in the case of "sat", at s.model(). 
    isSat = sq.check()
    
    # If the constraint is satisfiable return model  
    if (isSat == sat):
        return sq.model()
    # otherwise return Python's "None" value
    return None

# Set up and run the function and report its results
res = shapeq()
if (res == None) :
    print("There is no solution")
else :
    print("A solution is ", res)
