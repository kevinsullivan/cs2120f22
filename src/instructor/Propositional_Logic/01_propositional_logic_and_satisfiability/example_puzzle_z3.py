# Ack: https://medium.com/galileo-onwards/logic-puzzle-2-74e0166a4176
# From Hy Conrad’s Giant Book of Whodunit Puzzles (1999, pg 115–6). 

from z3 import *

# In the code Guilty is True and
# Innocent is Not Guilty.(
C, D, E, H, M = Bools(["Chase", "Decker", "Ellis", "Heath","Mullaney",])

s = Solver()

# 1. At least one suspect is guilty
s.add(Or(C,D,H,M,E))

# 2. If Chase is guilty and 
#       Heath is innocent
#    then Decker is guilty
s.add(Implies(And(C, Not(H)), D))

# 3. If Chase is innocent
#    then Mullaney is innocent
s.add(Implies(Not(C), Not(M)))

# 4. If Heath is guilty
#    then Mullaney is guilty
s.add(Implies(H,M))

# 5. Chase and Heath are not both guilty
s.add(Not(And(C, H)))


# 6. Unless Heath is guilty
#    then Decker is innocent
s.add(Implies(Not(H), Not(D)))


# Check for a model and return sat or unsat
satis = s.check()

# if the "model checking" found a solution
# then say so and give it, or say no such thing.
if (satis == sat) :
    print("There's a solution! ", s.model())
else :
    print("There is no solution!")