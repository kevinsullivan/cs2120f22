/-
This lecture extends what you have learned
by introducing the concept that existential
quantification is an "information hiding"
abstraction mechanism. To build a proof
of ∃ x, P x, you have to give a specific 
value for x; but when you eliminate from 
a proof of ∃ x, P x, all you get is some
arbitrary but specific value (aka general)
value, along with a proof that that value
has the stated property, P. The specific
value that was presumably used to build
the proof is no longer available. It has
been abstracted away, and elimination is
not able to recover it. 
-/

/-
Let's see this idea in action.

We'll represent a *property* objects of
a  type, α, as a *predicate* on α values.
(Using α is cooler than using T as a type
valued variable.) 

Here we'll juse use our simple evenness
one-place predicate on natural numbers. 
It is satisfied by any natural number,
n, such that n % 2 is zero.
-/

def ev (n : ℕ) : Prop := n % 2 = 0
#check ev  -- predicate: nat → Prop

/-
Here we'll formalize and prove a simple
theorem that says that if you assume
(or are given) (1) a natural number, n, 
and (2), a proof, pf, of (ev n), then 
you can prove ∃ n, ev n: that *there
exists* an even natural number. You do
it of course by applying the introduction
rule for exists to n as a witness and pf
as the corresponding required proof.
The main point of this example is just
to remind you exactly how exists.intro
works. 
-/
theorem 
ex_ev_n (n : ℕ) (pf : ev n) : 
  ∃ (m : ℕ), ev m := 
  ⟨ n, pf ⟩   -- exists.intro n pf


/-
Ok, great, so now what can we do with
such a theorem? Well, this particular
is a universal generalization, in the
sense that it takes any natural number
and any corresponding proof that that
*particular* number is even and gives
you something else in return, a proof
of ∃ n, ev n.

Here, for example, is a proof that there
exists an even number with 4 as a witness.
-/

#check ex_ev_n 4 rfl 

def pf_ex : ∃ (n : ℕ), ev n := 
  ex_ev_n 4 rfl

/-
Four happens to be the witness used to build
a proof of ∃ x, ev x, in this case; but from
this proof one can no longer recover that 4. 
Existential proofs "abstract away" the values
used to construct them. In particular, one
doesn't say, "There exists an x that satisfies
P, and here is one, w, along with a proof that
it does satisfy P. Rather such a proof just 
says, "There is some x with property, P and
can't say any more than that."
-/

/-
Now let's look at an example using Lean.

In this example we set ou to prove (∃ x, P x -> true) 
so that we can assume (get into our context a proof 
of) ∃ x, P x. Our aim isn't to prove true, but to see 
exactly what we can do with a such a proof. The answer
is that we can "eliminate" it to get (1) an arbitrary
but specific (general) value *with a name, such as w*,
along with a proof that that w has property P: a proof
of (P w). 
-/

example : (∃ (m : ℕ), ev m) → true :=   
begin
  assume h,           -- get ourselves proof of ∃ 
  cases h with w pf,  -- what case analysis does: 
                      -- one intro rule, one case,
                      -- with info about the args,
                      -- but no witness *details*.
  trivial,
end

/-
As you now already kno, the cases tactic applies 
the elimination rule for the given form of value.  
So, here, it applies or.elim (and a few clean-up
tactics). Put your cursor at the end of the cases
line and study the resulting context. You now have
a witness, w, of the right type, but you do *not*
have a specific value. You just have an arbitrary
value, albeit with a proof that it has the given
property.
-/

/-
The constraint that the elimination rule doesn't
reveal the witness, once it has been abstracted
away, is enforced by Lean's type system. Let's 
see what happen if we try to recover the natural
number, m, "inside" a proof of (∃ (m : ℕ), ev m).

Notice the crucial difference in the type of the
following implication/function. Whereas above we 
wanted a proof of (∃ (m : ℕ), ev m) → true, a 
purely logical proposition, how we're trying to
produce a proof of (∃ (m : ℕ), ev m) → nat. In
other words, we're trying to define a function
that takes a proof of an existential proposition
as an argument and that somehow then derives a
natural number from it. You might think that the
original witness is preserved in the proof, but
it's not. Again, that information is abstracted
away. 

Fortunately, Lean complains that you are "trying
to eliminate from a proof to a value of a type, 
T," where T is not Prop. What Lean is really 
saying is that you may not derive data values
from proofs. This restriction is part of Lean's 
approach to assuring the principle of "proof
irrelevance." Any proof is as good as any other,
and equivalent in all respects. If we could get 
4 from one ∃ proof and 5 from another, then this
principle would break: we'd be able to tell the
proofs apart, which our logic cannot let us do. 
-/

example : (∃ (m : ℕ), ev m) → nat :=   
begin
  assume h,           -- get ourselves proof of ∃ 
  cases h with w pf,  -- here's where you get caught
  trivial,
end

/-
What Lean is saying is that it's alright from a
proof of (∃ (m : ℕ), ev m) to derive a proof of
true, because true lives in the type, Prop. On
the other hand, nat lives in the type, Type, and
the rules of predicate logic do not allow one to
recover a computationally relevant value from a
proof of ∃ x, P. (I'm dropping the P x notation.)
In this way Lean enforces the abstracting nature
of existential quantification. Think about that
and try to really understand what it means. The
concept of information hiding abstraction is at
the heart of mathematics and programming. Here
you see a particularly simple exampe of it.
-/