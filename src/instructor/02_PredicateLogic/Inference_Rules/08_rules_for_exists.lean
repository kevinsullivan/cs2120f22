/- OVERVIEW

To readily understand the introduction rule and the
elimination rule for proofs of existential propositions
(starting with ∃), we first need a review of predicates.
Predicate in turn are thought of as functions from the
arguments to propositions "about" those arguments. So 
we also discuss function definitions, more generally,
and how we can specify them in various ways in Lean.
Finally we come back to the inference rules for ∃.
-/



/- ************************ -/

/- PREDICATES

A predicate is a proposition with one or more parameters.
A proposition is a predicate with no remaining parameters!

You can think of a predicate it as a function that takes
one or more arguments and that reduces to a proposition
*about those particular values*. 

Here, for example, we define a predicate, called isEven,
that takes a natural number, n, as an argument and that
reduces to ("returns") the proposition, n % 2 = 0, *for
that particular n*.
-/

def isEven : ℕ → Prop :=
begin
assume n,
exact (n%2 = 0)
end 

/-
In fact, in Lean and similar logical programming systems,
a predicate *is* a function, and can thus be applied to an
argument of the specified type.
-/

#reduce isEven 0      -- 0 = 0
#reduce isEven 1      -- 1 = 0
#reduce isEven 2      -- 0 = 0
#reduce isEven 3      -- 1 = 0

/-
Note that the n%2 expression is evaluated automatically.
-/

/-
We will say that one or more values "satisfy" a predicate
when the corresponding proposition is true. In constructive
logic, that means when there's a proof of that proposition.
-/

example : isEven 0 :=
begin
simp [isEven],  -- new tactic: simplify by def'n of isEven
exact rfl,      -- forces reduction, tests equality
-- Yay! 0 is even
end


-- The rfl tactic does some simplification automatically
example : isEven 0 :=
begin
exact rfl,      -- forces reduction, tests equality
-- Yay! 0 is even
end

example : isEven 1 :=
begin
exact rfl,      -- there's no proof of 1=0
-- Ooooh noooo, 1 is not even
end

-- In fact we can prove the negation
example : ¬isEven 1 :=
begin
assume h,
simp [isEven] at h, -- more tactic fun (optional)
cases h,            -- no proofs of h so done
-- Yay! 1 is *not* even (proof by negation)
end

-- Proof that 2 is even
example : isEven 2 :=
begin
exact rfl,
-- Yay! 2 is even.
end

/-
A predicate expresses a *property* of the objects
it takes as arguments. Here the predicate expresses
the property of a natural number *being even* (or not).
Every natural number, n, for which there is a proof
of isEven n has the property expressed by isEven, 
while every number, n, for which there is no proof of
isEven n, lacks the property specified by isEven. 

In this sense, as mentioned in class, a predicate 
also specifies a *set* of values: in this example, 
the set of all values, n, for which isEven n has a 
proof (and is thus true).
-/



/- ************************ -/

/- FUNCTIONS

Predicates are like functions, and indeed in
Lean are functions. The same ideas we've just
reviewed about predicates applies to functions,
more generally. 

Of high importance right now is the idea that
the syntax of predicate logic includes function
names and applications. A function applied to 
arguments of the right types designates some
other value, the return result. For example, 
in a logic of geneology, we might have a 
function called motherOf p, where p is a person
and the return result is the person who is the
mother of p. Let's call her m. Then the term
(motherOf p), a function application, is really
just another expression for m!

We are not mainly teaching Lean. We are teaching
predicate logic! Lean supports predicate logic. 
We are using Lean to help teach these concepts,
and moreover to teach them in a way that makes a
lot of sense for computer science students, using
a proof assistant, namely Lean.

So now we need to review and extend our knowledge
of Lean syntax (yes there is a little to learn)
for defining functions more generally. We'll stick
with the same "predicate function", isEven, example,
implementing it in various ways, and just giving
different names to these different versions to 
avoid name conflicts.
-/

/- 
You can use tactic scripts to define functions,
as above, but you can also write exact function
implementation terms.
-/

def isEven1 : ℕ → Prop := fun n, n % 2 = 0
def isEven2 : ℕ → Prop := λ n,   n % 2 = 0 

/-
You can pronounce the terms to the right of 
the := as "a function that takes an argument,
n, and returns the proposition, n % 2 := 0."
You can add type judgments either for clarity
or if Lean can't infer them from the context.
def isEven : ℕ → Prop := λ (n : ℕ), n%2 = 0.

The fundamental purpose of the λ/fun keyword is
to *bind names to arguments* so that they can be
used in the body/definition of a function. In
this case, we use λ/fun to bind the name n to 
the actual parameter value when this function is
applied to some argument. All of the n's in the
definition are then replaced by that value, and
the resuling expression is reduced to produce a
final result.  

The fun and λ keywords are exactly equivalent.
The use of "lambda" notation goes way back to 
the early days of CS. A key insight that you 
should take away is that "functions are values
too," and a "lambda expression" is a constant,
or literal value, the type of which is just a
function of some kind.
-/

/-
In Lean, you can move argument declarations to
the left of the colon and give them names there,
just as you would in Java or Python.
-/

def isEven3 (n : ℕ) : Prop := n % 2 = 0

/-
And as usual, you can leave out type judgments
when Lean can infer them from context.
-/

def isEven4 (n) := n % 2 = 0 -- parens required

/-
Finally, in Lean, you can use a construct called
"pattern matching" to define functions "by cases."
Here's the syntax. We'll use this syntax quite a
bit going forward, so best to get used to it now. 
-/

def isEven5 : ℕ → Prop    -- NB: No := used here
| n := n % 2 = 0

/-
Here, the "n" is bound to any value of the argument
type, and is then used to define the "return value"
to the right of the :=. In general we can use this
method of function definition to define returns for
different values or combinations of argument values.
-/

def my_bool_and : bool → bool → bool 
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := ff

def my_bool_and2 : bool → bool → bool 
| tt tt := tt
| _ _ := ff

/-
Functions in Lean must be "total," which means that
they must be defined to return values of the right
types for *all* possible combinations of arguments.
Go ahead and add the missing cases, then apply your
function!
-/

#eval my_bool_and tt tt
#eval my_bool_and tt ff
#eval my_bool_and ff tt
#eval my_bool_and ff ff

example : my_bool_and tt tt = tt := rfl
example : my_bool_and tt ff = ff := rfl
example : my_bool_and ff tt = ff := rfl
example : my_bool_and ff ff = ff := rfl

def my_bool_not : bool → bool 
| tt := ff
| ff := tt 

example : my_bool_not ff = tt := rfl
example : my_bool_not tt = ff := rfl 

/-
You should (almost must) use this "by cases" syntax
to define functions recursive functions. If you use
other syntax, you'll find that you won't be able to
have the function body call the function itself.
-/

def factorial' (n : ℕ) : ℕ :=
  if n = 0 
  then 1 
  else n * factorial' (n-1)      -- factorial not defined


def factorial : ℕ → ℕ           -- remember, no := here
| 0 := 1
| (n' + 1) := (n' + 1) * factorial n'


-- Lean can't prove termination recursive call is passed f(n) for some function, n
def factorial2 : ℕ → ℕ           -- remember, no := here
| 0 := 1
| n := n * factorial2 (n-1)     -- can't prove termination

/-
The problem with the preceding code, for reasons we
can't really get into very deeply right now, is that
Lean can't tell that the argument to factorial2 will
decrease in value on each recursive call, because all
it sees is a function (subtraction) applied to n, and
it doesn't try to analyze the result. On the other
hand, if n = (n' + 1), Lean knows that n' is one
smaller than n, so if n is the argument into the
function and it calls itself recursively to n', it
Lean will "see" that the argument passed to the
recursive call is always less than n, and so it can
guarantee the recursion terminates (with the base
case). 
-/

#eval factorial 5



/- ************************ -/

/- INFERENCE RULES FOR ∃ PROPOSITIONS

There are two inference rules for ∃ propositions: 
one introduction, one elimination. In Lean they are
called exists.intro and exists.elim. We will usually
use the cases tactic to apply the elimintion rule and
clean up the results. We generally apply the intro
rule directly. 
-/

/- Introduction Rule for ∃ 

Let's start with introduction. We give several proofs
of the proposition that "there exists n even number."
To construct such proof, one applies the introduction
rule to two arguments: a particular number, n, and a
proof that *that* number is even. As you can see in the
next three examples, it doesn't matter what number you
give as a first argument, as long as you can give a proof
that it's even as it's second argument. This works for
the first argument values of 6 and 8 (because there are
easy proofs that they're even) but not for 7 (because
it's not even).
-/

example : ∃ (n : ℕ), isEven n := 
  exists.intro 6 rfl           -- 6 is good witness

example : ∃ (n : ℕ), isEven n := 
  exists.intro 7 rfl           -- no proof 7 is even

example : ∃ (n : ℕ), isEven n := 
  exists.intro 8 rfl           -- 8 is good, etc.

/-
In summary, to prove ∃ (x : T), P x, apply exists.intro
to a particular value, (t : T), and to a proof of (P t),
that that particular value, t, has the property (e.g.,
of being even) specified by the predicate, P.
-/

/- Elimination rule for ∃

Now for the elimination rule. What can we deduce or derive
from a given proof of ∃ (x : T), P x? Simply put, we can
deduce that, for some particular but otherwise unspecified
value, w : T, there is also a proof of P w, that w has the
property in question.
-/

/-
Here's a trivial example, where we will assume we have a proof
of an existentially quantified proposition, just to see what we
can do with it.
-/
example : (∃ (n : ℕ), isEven n) → true :=
begin
assume h,
cases h with w pf,
-- that illustrates the point we wanted to make
-- look at the context: you deduced that there is
-- a "w" for which there's also a proof of isEven w.
end



/-
Here's a more interesting example. We prove that
"if there's a ball that's both blue and round then
there is a ball that's blue." 
  
How would you prove this in English? Well, from 
the assumption that there's a ball that has both
properties, we can deduce there's some specific
ball, w, for which there is a also proof of the
proposition, isBlue w ∧ isRound w, *about that
specific ball*. 

We can "eliminate" the ∧ to obtain separate 
proofs of isBlue w and isRound w. Then we can
finish the proof by applying exist.intro to that
same ball, w, and to a proof that it's blue. That
proves that there exists a blue ball, which is 
what we wanted to prove. QED. 
-/

-- Here's exact that argument formally
example 
  (Ball : Type)                             -- There is a type of object, Ball
  (isBlue : Ball → Prop)                    -- a predicate on objects of this type
  (isRound : Ball → Prop) :                 -- a second predicate on objects of this type
  (∃ (b : Ball), isBlue b ∧ isRound b) →    -- if there's a ball that satisfies both
  (∃ (b : Ball), isBlue b) :=               -- then there's a ball that satisfies one
begin
  assume h,                                 -- assume there's a ball that's blue and round
  cases h with b br,                        -- derive a specific ball, w, and a proof, br 
  cases br with blue round,                 -- split the proof of the conjunction into parts
  exact exists.intro b blue,                -- construct a proof that there's a blue ball
end

/-
Here are (our local versions of) the intro and elim 
inference rules for ∃. Before each one we use #check
to display Lean's "native" version.
-/

-- ∃ introduction

#check @exists.intro      -- Think of "Sort u" as just Type 

def exists_intro := 
  ∀ {X : Type}            -- for any type, X 
    {P : X → Prop}        -- for any predicate on values of this type
    (w : X),                -- if you give a witness w
    P w →                   -- then if you give a proof that w satisfies P
    (∃ (x : X), P x)        -- you get a proof there exists an x that satisfes P


-- ∃ elimination

#check @exists.elim

def exists_elim := 
  ∀ {X : Type}              -- for any type, X 
    {P : X → Prop}          -- for any predicate on values of this type
    {Y : Prop},             -- for any "concluding" proposition, Y
    (∃ (x : X), P x) →      -- if we're given a proof that there's an x satisfying P
    (∀ (x : X), P x → Y) →  -- then if for every x that satisfies P Y is true
    Y                       -- then Y is true

/-
Just glancing at this defintion doesn't
make it immediately clear that it "does the
same thing as the cases tactic." Let's see
that it does the same thing. We'll go back
to our very simpler example.
-/

example : (∃ (n : ℕ), isEven n) → true :=
begin
assume h,   -- assume a proof that there an even number
/-
The cases tactic eliminate h and leaves us
with w and pf as a specific but unspecifiedn
number, w, and proof that it's even. You can
uncomment the next line and see that work.
-/
-- cases h with w pf,
/-
If instead we apply exist.elim directly, we
just need to do a little "cleanup" to get to
the same point.
-/
apply exists.elim h,  -- Lean picks names
assume w,             -- we'll call witness w
/-
The next thing we will assume is that we're 
given a proof of "isEven w." It doesn't look
like that, but that's what it says. 

The expression "(λ (n : ℕ), isEven n)" is a
function that takes a natural number, n, as
an argument and returns the proposition, 
isEven n. Now this function is applied to w,
yielding the proposition, isEven w. And 
because this entire expression is the premise
of an implication, we'll assume we have a 
value of this type, i.e., a proof of isEven w.
-/
assume pf,      -- there it is, as expected!
-- the rest of a real proof proceeds from here.
-- We recommend just using the cases tactic.
-- It does exists.elim and two "assumes" for you 
end


/-
Question: Would the preceding proposition be true 
if you just dropped the condition, (∃ (x : X), P x)? 
The answer is no, but why? There's an edge case that
the existence proof eliminates. What's the edge case? 
-/
