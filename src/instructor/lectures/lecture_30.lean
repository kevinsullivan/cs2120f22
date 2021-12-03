/- LISTS

Lists are defined very much like natural numbers
with the following difference: a natural number is
either zero or succ applied to a ("smaller") natural
number. The latter term, (succ n), represents n+1.
A list by contrast is either empty, or it's cons
applied to (a) a value, a, of some type, α, which
is the type of the elements in the list, and (b) a
"smaller" list of the same kind (of type "list α"). 
So just as every non-zero nat has a one-smaller nat
"inside" of it, every non-empty list has a smaller
list (along with a new element at the head of the
new list) inside of it.

As a consequence, functions and proofs for lists 
will be very much like functions (recursive) and
proofs (by induction) for natural numbers.
-/

namespace hidden 

inductive list (α : Type) : Type 
| nil : list
| cons (h : α) (t : list) : list

end hidden