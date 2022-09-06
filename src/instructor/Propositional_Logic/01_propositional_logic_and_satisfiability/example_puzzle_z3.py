from z3 import *

# In the code Guilty is True and
# Innocent is Not Guilty.(
Chase, Decker, Ellis, Heath, Mullaney = z3.Bools(
    [
        "Chase",
        "Decker",
        "Ellis",
        "Heath",
        "Mullaney",
    ])

s = Solver()

# 1. at least one is guilty
s.add(
    (Chase == True)
    or (Decker == True)
    or (Heath == True)
    or (Mullaney == True)
    or (Ellis == True)
)

# 2. if Chase is guilty
#        and Heath is innocent
#    then Decker is guilty
s.add(
    z3.If(
        Chase == True    # condition
        and Heath != True,
        Decker == True,  # then
        True,            # else
    )
)

# 3. if Chase is innocent
#    then Mullaney is innocent
s.add(
    z3.Implies(
        Chase != True,
        Mullaney != True
    )
)

# 4. if Heath is guilty
#    then Mullaney is guilty
s.add(
    z3.Implies(
        Heath == True,
        Mullaney == True
    )
)

# 5. Chase and Heath are not both guilty
s.add(
    z3.Not(
        Chase == True
        and Heath == True
    )
)

# 6. Unless Heath is guilty
#    then Decker is innocent
s.add(
    z3.If(
        Heath == True,
        True,
        Decker != True,
    )
)

satis = s.check()
if (satis == sat) :
    print("There's a solution! ", s.model())
else :
    print("There is no solution!")