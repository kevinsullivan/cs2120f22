/- OBJECTS 

For example, consider the set, written in 
what's called display notation: { 1, 2, 3, 4 }.

The set has four members, as enumerated here.
A key distinction is between the type of the
elements of a set, here ℕ, and the type of the 
set, itself, here, set ℕ.
-/

/- OPERATIONS

Assume that we've been given some type, T. The 
algebraic structure set T includes the following
constants and operations:

membership (s : set T) (v : T) : is v in s?
empty set -- containing no elements of type T
complete set -- containing all T-valued elts
complement (s : set T) : set T  -- not in s
subset (s1 s2 : set T) : Prop
difference (s1 s2 : set T) : set T -- in s1 not s2
union (s1 s2 : set T) : set T   -- in either
intersection (s1 s2 : set T) : set T -- in both
product (s1 : set T) (s2 : set V) : set (T × V)
power (s : set T) : set (set T) -- set of subsets
-/

/- membership: 

Membership in a set, s, is defined by a predicate:
one that's satisfied by (true for) all and only the
element values considered to be "in" s. Indeed, we
can represent a set by its predicate, and that's 
just what we're now going to do. Think of a set as
a predicate, applicable to a potential member, and
yielding a true proposition is the value is in the
set and a false proposition otherwise.

Let's revisit our favorite one-place predicate, the
evenness predicated, ev, on values of type ℕ. We can
now think of this predicate as (defining) a set: the
set of all even natural numbers! Indeed, we have a
notation for sets defined explicitly by predicates.
-/

def ev (n : ℕ) : Prop := n % 2 = 0

def even_nat_set : set ℕ := { n : ℕ | ev n }

/-
Let's pronounce that in English. We define even_nat_set
to be (bound to) a value of type, set ℕ, representing a
set of natural numbers, namely the set of values, n, of
type nat, such that ev n (is true). In other words, we
define even_nat_set as the set of natural numbers that
satisfy the (ev _) predicate.

This is the crucial notion. It both builds immediately
on everything we've covered up to now, and it gives us
a strong foundation to make sense of sets as objects
that we can define and reason about using logic and
proofs.
-/

-- The type, set T, actually just means T → Prop!
def even_nat_set' : ℕ → Prop := { n : ℕ | ev n }
-- notice we changed the apparent type to ℕ → Prop
-- but use "set T" because it provides set notation

/- 
{ n : ℕ | ev n } is notation for a predicate,
of type ℕ → Prop, that when applied to nat, n, 
yields the proposition, ev n. Here we write it
in yet another form, as an ordinary function.
-/
def even_nat_set'' ( n : ℕ) : Prop := ev n

/-
There are many ways to write such a predicate.
Here we use a tactic script (to write a function!)
-/
def even_nat_set''' : ℕ → Prop := 
begin
  assume (n : ℕ),   -- assume we're given a data value!
  exact ev n        -- return corresponding proposition
                    -- voila, our predicate 
end

/-
All of the preceding definitions are equivalent.
They all define the set of even numbers. It's an
infinite set, of course, so we can't possibly just
enumerate all of its elements. Our trick then is
to define the set by giving a predicate that all
and only the desired values will satisfy -- here
all and only even natural numbers.
-/

/- empty set: 

The empty set of values of a given type T is the set
containing no elements. It must thus be defined by a
one-place predicate that is not satisfied by *any* 
values of the element type. If the element type is T,
what exactly is this predicate? To be more concrete,
if the element type is ℕ, what is the predicate that
defines the set containing no elements? 
-/

def empty_set_nat : set ℕ := _


/- CHANGE IN PERSPECTIVE!
We will now think of a set as being
defined defined by its membership predicate.
-/

def s1 : set ℕ := { n : ℕ | n = 0 }

#check s1
#reduce s1

#check s1 0
#reduce s1 0
#reduce s1 1
#reduce s1 2
#reduce s1 3

/-
In a sense that we can now make precise,
this *predicate* defines a set: the set 
of all natural numbers that *satisfy* it. 
We can think of ev as being a membership
predicate that indicates whether a given
value is in a given set or not. 

It should be clear that every predicate
can be understood as defining a set: the
set of values that satisfy the predicate.  

The next section of the course introduces
the lovely topic of set theory based exactly
on this idea: represent sets as predicates,
and operations on sets (such as intersection
and union) as corresponding to operations on 
predicates. 

Indeed we will define the type "set T" just
to be the predicate T → Prop! A set is thus
represented *exactly* as a predicate in our
logic. 
-/


-- set comprehension notation
def s0  : set ℕ  :=  { n : ℕ | ev n }


--We can prove these two
example : s0 0 := rfl
example : s0 2 := rfl

-- But not these two
example : s0 1 := rfl
example : s0 3 := rfl

-- set membership notation
-- v ∈ s just means s v

#reduce 0 ∈ s0  -- yes 
#reduce 1 ∈ s0  -- no
#reduce 2 ∈ s0  -- yes
#reduce 3 ∈ s0  -- no

example : 0 ∈ s0 := rfl -- why rfl?
example : 2 ∈ s0 := rfl -- why rfl?

example : 1 ∉ s0 := 
begin
  assume h,
  cases h,
end

example : 3 ∈ s0  := 
begin
  show s0 3,
  show ev 3,
  simp [ev],
  show 1 = 0,
  -- stuck
end

-- set display notation
def s1'' : set nat := { 1, 2, 3, 4 }
def s1''' := {1, 2, 3, 4} -- need explicit type


