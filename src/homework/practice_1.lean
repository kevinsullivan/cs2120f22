/-
EQUALITY
-/

/- #1 
Suppose that x, y, z, and w are arbitrary objects of some type, 
T; and suppose further that we know (have proofs of the facts) 
that  x = y, y = z, and w = z. Give a very, very short English 
proof of the conjecture that z = w. You can use not only the 
axioms of equality, but either of the theorems about properties 
of equality that we have proven. Hint: There's something about
this question that makes it much easier to answer than it might
at first appear.
-/



/- #2
Give a formal statement of the conjecture (proposition) from
#1 by filling in the "hole" in the following definition. The
def is a keyword. The name you're binding to your proposition
is prop_1. The type of the value is Prop (which is the type of
all propositions in Lean). 
-/

def prop_1 : Prop := 
  _

/- #3 (extra credit)
Give a formal proof of the proposition from #2 by filling in
the hole in this next definition. Hint: Use Lean's versions of
the axioms and basic theorems concerning equality. They are,
again, called eq.refl, eq.subst, eq.symm, eq.trans.
-/

theorem prop_1_proof : prop_1 := 
begin
  _
end

/-
FOR ALL: ∀. 
-/

/- #4
Give a very brief explanation in English of the introduction
rule for ∀. For example, suppose you need to prove (∀ x, P x);
what do you do? (I'm being a little informal in leaving out the
type of X.) 
-/

/- #5
Suppose you have a proof, let's call it pf, of the proposition,
(∀ x, P x), and you need a proof of P t, for some particular t.
Write an expression then uses the elimination rule for ∀ to get
such a proof. Complete the answer by replacing the underscores
in the following expression: ( _ _ ). 
-/

/-
IMPLIES: →

In the "code" that follows, we define two predicates, each 
taking one natural number as an argument. We call them ev and 
odd. When applied to any value, n, ev yields the proposition 
that n is even (n % 2 = 0), while odd yields the proposition
that n is odd (n % 2 = 1).
-/

def ev (n : ℕ) := n % 2 = 0
def odd (n : ℕ) := n % 2 = 1 

/- #6
Write a formal version of the proposition that, for *any* 
natural number n, *if* n is even, *then* n + 1 is odd. Give 
your answer by filling the hole in the following definition. 
Hint: put parenthesis around "n + 1" in your answer.
-/

def successor_of_even_is_odd : Prop := 
  _

/- #7
Suppose that "its_raining" and "the_streets_are_wet" are
propositions. (We formalize these assumptions as axioms in
what follows. Then give a formal definition of the (larger)
proposition, "if it's raining out then the streets are wet")
by filling in the hole
-/

axioms (raining streets_wet : Prop)

axiom if_raining_then_streets_wet : _
  

/- #9
Now suppose that in addition, its_raining is true, and
we have a proof of it, pf_its_raining. Again, we again give
you this assumption formally as an axiom below. Finish
the formal proof that the streets must be wet. Hint: here
you are asked to use the elimination rule for →. 
-/

axiom pf_raining : raining

example : streets_wet :=
 _

/- 
AND: ∧
-/

/- #10
In our last class, we proved that "∧ is *commutative*."
That is, for any given *propositions*, P and Q, (P ∧ Q) → 
(Q ∧ P). The way we proved it was to *assume* that we're 
given such a P, Q, and proof, pq, of (P ∧ Q) -- applying
the introduction rules for ∀ and →). In this context, we
*use* the proof, pq, to derive separate proofs, let's call
them p, a proof of P, and q, a proof of Q. With these in
hand, we then apply the introduction rule for ∧ to put 
them back together into a proof of (Q ∧ P). We give you
a formal version of this proof as a reminder, next.  
-/

theorem and_commutative : ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q pq,
  apply and.intro _ _,
  exact (and.elim_right pq),
  exact (and.elim_left pq),
end

/-
Your task now is to prove the theorem, "∧ is *associative*."
What this means is that for arbitrary propositions, P, Q, and
R, if (P ∧ (Q ∧ R)) is true, then ((P ∧ Q) ∧ R) is true, *and
vice versa*. You just need to prove it in the first direction.
Hint, if you have a proof, p_qr, of (P ∧ (Q ∧ R)), then the
application of and.elim_left will give you a proof of P, and
and.elim_right will give you a proof of (Q ∧ R). 
To help you along, we give you the first part of the proof,
including an example of a new Lean tactic called have, which
allows you to give a name to a new value in the middle of a
proof script.
-/

theorem and_associative : 
  ∀ (P Q R : Prop),
  (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R) :=
begin
  intros P Q R h,
  have p : P := and.elim_left h,
end

/- #11
Give an English language proof of the preceding
theorem. Do it by finishing off the following
partial "proof explanation."

Proof. We assume that P, Q, and R are arbitrary 
but specific propositions, and that we have a
proof, let's call it p_qr, of (P ∧ (Q ∧ R)) [by
application of ∧ and → introduction.] What now
remains to be proved is ((P ∧ Q) ∧ R). We can
construct a proof of this proposition by applying
_____ to a proof of (P ∧ Q) and a proof of R.
What remains, then, is to obtain these proofs.
But this is easily done by the application of
____ to ____. QED. 
-/


/-
Note that Lean includes versions of these
theorems (and many, many, many others) in 
its extensive library of formalized maths, 
as the following check commands reveal.
Note the difference in naming relative to
the definitions we give in this file.
-/
#check @and.comm
#check @and.assoc