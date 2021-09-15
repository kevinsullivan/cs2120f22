/-
-/

theorem and_associative : 
  ∀ (P Q R : Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
begin
  assume P Q R,
  assume h,
  have pq : P ∧ Q := and.elim_left h,
  have p : P := and.elim_left pq,
  have q : Q := and.elim_right pq,
  have r : R := and.elim_right h,
  exact and.intro p (and.intro q r),
end

/-
The or connective, ∨, in predicate logic
join any two propositions, P, Q, into a
larger proposition, P ∨ Q. This proposition
is judged as true if either (or both) P, Q
are true.
-/

/-
Introduction rules (two of them).

There are two ways to prove a proposition,
(P ∨ Q): with a proof of P, or with a proof
of Q. Either will do. We thus have two intro
rules for ∨. They are called the left and
right introduction rules. 

The left one takes a proof, let's say, p, of 
the left proposition, P (from which it infers) 
P along with the right proposition, Q, and then 
returns a proof of P ∨ Q. The arguments are 
actually given in the other order. The right 
introduction rule thus takes the proposition, 
P and a proof of the proposition, Q, and also
returns a proof of P ∨ Q.

Exercise: Suppose that it's true (and thus
that we we have a proof) that Joe chews gum. 
Give an English proof of the proposition that
(Joe is tall) ∨ (Joe chews gum).

Proof: Apply the right introduction rule for
∨ to (1) our proof that Joe chews gum, and
(2) the proposition that Joe is tall. The 
result is the proof we want, of the proposition 
(Joe chews gum) ∨ (Joe is tall).

Exercise: Give an English language proof of:
(Joe is tall) ∨ (Joe chews gum).
-/

/-
In Lean, the rules are called or.intro_left
and or.intro_right.
-/

#check @or.intro_left
#check @or.intro_right

/-
In the preceding outputs, you can see that the
arguments that are required explicitly are in
parentheses, and the arguments whose values are
inferred from other arguments are given in {}.
-/

/-
Let's formalize our example in Lean.
-/

axioms (Joe_is_tall Joe_chews_gum : Prop)
axiom jcg: Joe_chews_gum

theorem jcg_or_jit: Joe_chews_gum ∨ Joe_is_tall :=
  or.intro_left Joe_is_tall jcg 

/-
We thus have two inference rules (axioms) that we
can use to create a proof of a "disjunction". 

(Q : Prop) {P : Prop} (p : P)
----------------------------- ∨ intro_left
        pf : P ∨ Q

(P : Prop) {Q : Prop} (q : Q)
----------------------------- ∨ intro_right
        pf : P ∨ Q
-/

/-
Suppose that if Joe is tall then he is funny,
that if Joe chews gum he is also funny, and that
Joe chews gum ∨ Joe is tall. What can we deduce
from these assumptions/facts? 
-/

/-
You have just used the elimination rule for ∨. 
Here it is a little more generally. Suppose P,
Q, and R are propositions, that P → R and Q → R, 
and finally that P ∨ Q is true? What can we then
deduce? Why, R, of course!

{P Q R : Prop} (pq : P ∨ Q) (pr : P → R) (qr : Q → R) 
-----------------------------------------------------
                        pf : R
-/

#check @or.elim

/-
Let's add a few assumptions and see this rule in action.
-/
axioms (P Q R : Prop) (pq : P ∨ Q) (pr : P → R) (qr : Q → R) 

example : R := _

axioms 
  (Joe_is_funny : Prop) 
  (torf : Joe_is_tall ∨ Joe_chews_gum)
  (tf: Joe_is_tall → Joe_is_funny)
  (gf : Joe_chews_gum → Joe_is_funny)

example : Joe_is_funny := 
  or.elim torf tf gf

/-
In English, under the given assumptions
(axioms, just above) we can prove that Joe
is funny *by cases*. We know that Joe chews
gum OR Joe is tall, so least one of these
cases must hold. Let's consider the cases
in turn. 

Case 1: Suppose that (Joe is tall ∨ Joe
chews gum) is true because Joe is tall.
In this case we apply the fact that (Joe
is tall → Joe is funny) to the fact hat
(Joe is tall) to deduce that Joe is funny.

Exercise: What inference rule did we use
right there?

Case 2: The reasoning is similar. Suppose
the disjunction is true because Joe chews
gum. We can use "modus ponens", applying
the fact that (Joe chews gum → Joe is funny)
to deduce (Joe is funny).

Therefore Joe is funny *in either case*, 
and *there are no other cases to consider*
so we can deduce that Joe is funny.
-/

/-
Here it is formally!
-/

-- By cases
example : Joe_is_funny :=
begin
  cases torf, -- applies or.elim
  apply tf h,
  apply gf h,
end

-- Equivalent direct application of or.elim
example : Joe_is_funny :=
begin
  apply or.elim torf _ _, -- applies or.elim
  exact tf,
  exact gf,
end

/-
Yay, now how about proving some theorems.
-/

/-
Problem #1: State precisely and prove that 
∨ is commutative, in English then formally.
-/

/-
Problem #2: State precisely and prove that ∨ 
is associative, first in English then formally.
-/