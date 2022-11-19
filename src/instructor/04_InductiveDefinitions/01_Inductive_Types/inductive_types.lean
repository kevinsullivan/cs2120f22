namespace cs2120

/-
Until this point in this class, we have
worked mostly "in Prop." That makes sense
because we were studying predicate logic.
We still are, but now that we know basic
reasoning principles, we're going to home
in on functions as an element of predicate
logic. Predicate logic supports function
symbols and applications to arguments with
particular meanings. Our constructive logic
provides the means, which you now already
most know, to define function, apply them
to arguments, and get results. It's really
very valuable to have an environment in
which you can do logical reasoning with
functions that actually compute! It makes 
it CS-like beyond just the philosophy.
-/

inductive empty : Type 

inductive unit : Type
| star

def unit_fun : unit → unit 
| u := u

open unit 

#eval unit_fun star

inductive my_bool : Type
| ttt
| fff

open my_bool

def my_bool_not : my_bool → my_bool
| ttt := fff
| fff := ttt

#reduce my_bool_not ttt 

end cs2120 




