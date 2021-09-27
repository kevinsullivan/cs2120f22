/-
In this lecture we began to pull together the big
picture of the language of predicate logic, proofs,
reasoning principles (axioms, theorems proved from
them). For each logical connective and quantifier,
we have zero or more introduction and elimination
rules. You absolutely have to understand all of 
them and be sufficiently practiced in their use so
as to employ them when solving new proof problems.  
-/

/-
In this lecture, we continue to fill in our chart
with a sharp focus on on negation elimination, a
topic new for us here. Negation elimination is a
bit of a misnomer, in the sense allow us to cancel
double negations. In this sense it is the heart of
what we call proof by contradiction.  

Recall that in a proof by negation, your goal is
to prove ¬P, for some proposition, P. To do so, 
you assume P, show that that leads to some kind
of contradiction, and conclude P → false. This
is the precondition for deducting ¬P. 

Proof by contradition is different. Here you want
to prove P. You do this by assuming ¬P, and then
you show that the assumption yields a contradiction,
thus showing ¬¬P. Negation elimination is the used
to deduce P (from ¬¬P).

The interesting fact, however, is that ¬¬P → P is
not a theorem in the constructive logic of the Lean
Prover. Rather, if this inference rule is to be used
in reasoning (and most mathematicians use it freely)
it has to be added as an axiom, or in the form of
another axiom that his this one as a consequence.

Here we accept a different axiom, the so-called law
of the excluded middle. It's really not a law, it's
just a useful axiom that we can add to our logic
without causing any inconsistencies/contradictions.
It's the use of the excluded middle (em) that makes
it possible to derive ¬¬P → P as a theorem. (The
truth is that you can assume either and derive the
other, so the turn out to be equivalent.)
-/


/-
The first two examples/problems from the homework
gave us material to review the concepts of negation,  
false, and case analysis on values of uninhabited 
types as a way to complete proofs "for free." (This
is false elimination.)
-/

/-
  0 ≠ 1 is just notation for
¬(0 = 1), and that is just notation for
 (0 = 1) → false
 The proposition to be proved is thus an implication
 We assume the premise
 The proof is then completed by case analysis on that assumption
 As there are zero ways to construct a proof of 0 = 1, we're done
-/
example : 0 ≠ 1 :=
begin
  assume h,
  cases h,
end


/-
From a false premise, anything follows. The proof here is 
more interesting. As we're to prove an implication, we first
assume the premise, 0 ≠ 0, and then need to show 2 = 3. 
Now 0 ≠ 0 means ¬(0 = 0), and that means (0 = 0) → false.
In other words, if we have a proof of 0 = 0, we can derive
a proof of false from it. But of course it's trivial to get
a proof of 0 = 0; it's just (eq.refl 0). We thus have what
we need to derive a proof of false, at which point we use
false elimination to be done. 
-/
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  exact false.elim (h (eq.refl 0)),
end


/-
As a warmup to proving our main theorem, ¬¬P → P, here
we prove its converse, P → ¬¬P. This proof turns out to
be pretty easy and well within reach in the logic of Lean
without any additional axioms.
-/
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f : false := h p,
  exact f,
end 

/-
Finally we come to the principle of negation
elimination and the directly related strategy
of proof by contradiction. Remember: you want
to prove P, so you assume ¬P, then show that
this leads to a contradiction, proving ¬¬P,
at which point you "go classical" and apply
the theorem/axiom of negation elimination to
conclude P.
-/

/-
Remarkably, this principle is neither an axiom
or a theorem in Lean. Nither is a related axiom,
the axiom of the excluded middle. Adding it is
easy: we declare this universal generalization
to have a proof, em, which makes it applicable
to *any* proposition, P, whatsoever. When so
applied, it yields is a *proof* of the r*elated*
proposition, P ∨ ¬P.
-/

axiom em : ∀ (P : Prop), P ∨ ¬P

/-
The "law" (axiom) of the excluded middle is a key
to proving many intuitive theorems in logic and 
mathematics. But it also has a cost in that the 
proofs it produces are "uninformative", where a
proof of P ∨ ¬P in Lean's constructive logic would
include a detailed proof one way or the other, all
the way down to the basic axioms of the logic. In
cases where code is to be extracted from proofs, 
you can imagine that having uninformative proofs
makes that task impossible, and you'd be right. 
-/

theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

/-
Remember, proof by contradiction is really (and 
literally) just applying the axiom of negation
elimination. You can see this priciple in action
right here.
-/

axiom P : Prop
theorem p : P :=
begin                 -- goal is to prove P
  apply neg_elim _,   -- with neg_elim it will suffice to prove ¬¬P
  assume np,          -- this entails assuming ¬P and deriving a contradiction
                      -- that's the essence of proof by contradiction
                      -- of course we have no information to finish this proof
end