/- LISTS

Lists are defined very much like natural numbers.
By lists, we mean values that we might write, say,
in Java, like this:
- [1, 2, 3]
- [tt, ff, ff]
- ["Hello", "Lean", "!"]
-/

#check [1,2,3]
#check [tt,ff,ff]
#check ["Hello","Lean","!"]

/-
A little background on lists. In Lean's type library
list is a polymorphic type, which means that it's a
type that takes another type as a parameter. So list
itself is not a type, rather it's like a function 
that takes a type, such as nat or bool, as an argument, 
(α : Type), and returns a complete type as a result, 
namely, list α, where α could be nat, bool, or any
other type. 
-/

#check @list
/-
You can right click on list and "go to definition" on
to see that Lean's definition of the list type is as 
follows. 
-/

-- THE LIST POLYMORPHIC DATA TYPE

namespace hidden
universe u                            -- ignore
inductive list (T : Type u)           --ignore the u
| nil : list
| cons (hd : T) (tl : list) : list
end hidden
/-
We put our definition in our own namespace to
avoid conflicting with Lean's definition. That
we "end"the namespace means that in what follow's 
we're using Lean's definition of list. Note that 
in Lean's library the type argument to list is 
called T not α. In this file we'll continue to 
use α. There is no difference in meaning, it's
just a change in the name of the parameter to
the list "type builder." 
-/

/-
Now let's look more carefully at the definition.
The type has two constructors, a constant, nil,
and cons hd tl. What the constructors (introduction 
rules!) say is that list.nil is (axiomatically) a
value of type list α; and that if hd (for "head") 
is of type α (an "element"), and tl (for "tail") 
is a  "smaller" value of type list α, then "cons 
hd tl" is also a list: namely the list with hd 
as its first element and tl as the rest of the 
list. 
-/

/-
Examples
-/

-- empty list, []
def l0 : list nat := list.nil -- shorthand: []
def l0' := @list.nil nat      -- alternative     

-- the list, [0,1,2]
def l1 :=         -- shorthand: [0,1,2]
  list.cons       -- takes two arguments
    0             -- an element value       
    (list.cons    -- and a smaller list
      1           -- head
      (list.cons  -- list
        2         -- head
        list.nil  -- list, done!
      )
    )

#reduce l1    -- Lean uses [] notation

-- Using Lean's list notation
def l1' := [0,1,2]  -- convenient notation

def l2 :=           -- [3,4]
  list.cons         -- cons takes two args
    3               -- element at head of new list 
    (list.cons      -- the "tail" list of new list
      4             -- the head of the smaller list
      list.nil      -- the tail of the smaller list
    )

-- FUNCTIONS ON LISTS

/-
Now just as we defined addition for natural numbers,
recursively, so we can define string "addition", which
we will call "append." Carefully compare this definition
with our (and Lean's) definition of nat.add.
-/

/-
The definition of append is recursive again with 
two cases: one where the first argument is nil, the 
empty list (like zero), and one where it is of the 
form cons h t (analogous to succ n'). 
-/

-- list "addition" aka  list "append"
namespace hidden
def append {α : Type} : list α → list α → list α 
| list.nil l := l
| (list.cons a t) l := list.cons a (append t l) 
end hidden 

def l3 := append l1 l2  -- using Lean's definition
def l3' := l1 ++ l2     -- infix notation for append
#reduce l3              -- it works! [0,1,2,3,4]
#reduce list.append l1 []
#reduce list.append [] l1
-- reduce can't deal well with strings, so #eval
#eval ["Hello", "Lean"] ++ ["!"]

-- PROPOSITIONS AND PROOFS ABOUT LISTS

/-
Proving that for any list l,
allending nil and l is l, is
easy, because this theorem is
given as an axiom by the first
rule in the definition of append.
"append list.nil l := l". 
-/
example : 
  ∀ (α : Type) (l : list α), 
  list.append list.nil l = l := 
begin
  assume α l,
  simp [list.append],
end

/-
Sadly, we don't have a rule
that defines nil as a  "right 
zero", such that for any list, 
l, append l nil = l. If we want 
to use this equality in reasoning 
we need a proof that it is true. 
We need it as a theorem (that we
have proved). 
-/

#check @list.append

example : 
  ∀ (α : Type) (l : list α), 
  list.append l list.nil = l := 
begin
  assume α l,
  simp [list.append],
end

/-
The proof is by induction on 
the first list argument. Let's
look at the induction principle
for list α.

Here's the induction principle for
lists. Make sure you can read and fully
understand what it's saying. It's very
similar to the rule for nat. 

list.rec_on :
  Π {α : Type}                      (1)
    {motive : list α → Sort u_1}    (2)
    (n : list α),                   (3)
    motive list.nil →               (4)
    (Π (h : α) (t : list α),        (5)
      motive t →                    (6)
      motive (list.cons h t)) →     (7)
    motive n                        (8)

It says 
that for any property ("motive") of 
lists of α values, for any natural 
number n, you can conclude (motive n),
which is to say, ∀ n, motive n, as 
long as you have proofs of the two
lemmas: you need to show that the
empty list has the property and that
if a list, t, has the property, then
for any new element, (h : α), the 
list, cons h t, has the property.

"Applying induction" to a list n reduces 
the problem of proving ∀ n, motive n, to 
the subproblems of proving a base case (4) 
and and inductive step lemma (5-7). This
looks a whole lot like the proof we used
to show that zero is a left zero as well
as a right zero for addition in on the 
natural numbers.  So let's formalize it.
-/

example : 
  ∀ {α : Type} (n : list α), append n list.nil = n :=
begin
  _       -- Your job!
end
