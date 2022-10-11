/-
CS2120 Fall 2022 Sullivan. Quiz #1. Edit your answers into
this file using VSCode. Save the file to your *local* hard 
drive (File > Save As > local > ...). Submit it to the Quiz1
assignment on Collab.
-/

-- Grading: 6 points per part. 15 for completely correct EC.


/-
#1: For each of the following questions give a yes/no answer 
and then a very brief explanation why that answer is correct.
To explain why your answer is correct, name the specific rule
of inference that tells you it's correct, or explain that 
there is no such valid inference rule.
-/

/-
#1A

If a ball, b, is round *and* b is also red, is b red?

A: yes/no: YES

B: Why? and elimination


#1B

If flowers make you happy and chocolates make you happy,
and I give you flowers *or* I give you chocolates, will
you be happy?

A: yes/no: Yes

B: Why? Or elimination


#1C: If giraffes are just zebras in disguise, then the 
moon is made of green cheese?

A. yes/: Yes

B. Why? False elimination


#1D. If x = y implies that 0 = 1, then is it true that
x ≠ y?

A. yes/no: Yes

B. Why? not introduction, proof by negation



#1E. If every zebra has stripes and Zoe is a Zebra then
Zoe has stripes.

A. yes/no: yes

B. Why? all elimination, universal specialization


#1F. If Z could be *any* Zebra and Z has stripes, then 
*every* Zebra has stripes.

A. Yes/no: yes

B: Why? all introduction


#1G. If whenever the wind blows, the leaves move, and 
the leaves are moving, then the wind is blowing.

A. yes/no: no

B. Why? not valid, someone could be shaking the tree
(affirming the conclusion)


#1H: If Gina is nice *or* Gina is tall, and Gina is nice,
then Gina is not tall. (The "or" here is understood to be
the or of predicate logic.)

A. yes/no: no

B. Why? not valid, Gina could be tall and nice 
(affirming the disjunct)
-/


/- 
#2

Consider the following formula/proposition in propositional
logic: X ∨ ¬Y.

#2A: Is is satisfiable? If so, give a model (a binding of 
the variables to values that makes the expressions true).

Yes. X = true and Y could be anything


#2B: Is it valid? Explain your answer. 

no: X = false and Y = true is a counterexample
-/


/-
#3: 

Express the following propositions in predicate logic, by
filling in the blank after the #check command.

If P and Q are arbitrary (any) propositions, then if (P is 
true if and only if Q is true) then if P is true then Q is 
true.
-/

#check ∀ (P Q : Prop), (P ↔ Q) → (P → Q)


/-
#4 Translate the following expressions into English.
The #check command can of course be ignored here. 
-/


-- A
#check ∀ (n m : ℕ), n < m → m - n > 0
#check ∀ (n m : ℕ), n < m → m - n > 0


/-
Answer: If n and m are any two natural numbers, then if 
n is less than m then the difference, m - n, is positive
-/

-- B

#check ∃ (n : ℕ), ∀ (m : nat), m >= n


/-
Answer: There's some natural number n that is less
than or equal to every other natural number. (And 
this is also true, by the way. The number n = 0.)
-/


-- C

variables (isEven: ℕ → Prop) (isOdd: ℕ → Prop)
#check ∀ (n : ℕ), isEven n ∨ isOdd n

/-
Answer: Every natural number is even or odd (or both).
(Note however that we haven't really defined what these
predicates mean here.)
-/


-- D

#check ∀ (P : Prop), P ∨ ¬P

/-
Answer: Every proposition is true or false. Note: this is
actually not an axiom/rule in constructive logic, though it
can be added as a rule without causing inconsistencies. By
adding it, we convert constructive predicate logic into
classical (albeit higher-order) predicate logic. We'll talk
more about this later.
-/


-- E

#check ∀ (P : Prop), ¬(P ∧ ¬P)

/-
Answer: No proposition can be both true and false.
-/


/-
#5 Extra Credit

Next we define contagion as a proof of a slightly long
proposition. Everything before the comma introduces new
terms, which are then used after the comma to state the
main content of the proposition. 

Using the names we've given to the variables to infer
real-world meanings, state what the logic means in plain
natural English. Please don't just give a verbatim reading
of the formal logic. 
-/

variable contagion : 
  ∀ (Animal : Type) 
  (hasVirus : Animal → Prop) 
  (a1 a2 : Animal) 
  (hasVirus : Animal → Prop)
  (closeContact : Animal → Animal → Prop), 
  hasVirus a1 → closeContact a1 a2 → hasVirus a2

/-
If any animal, a1, has a virus, and a1 comes in contact
with an animal, a2, then a2 will have (catch) the virus.
-/