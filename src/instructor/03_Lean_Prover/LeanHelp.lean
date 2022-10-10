/-
In this file, we provide detailed explanations and examples 
of the following constructs in Lean.

#check
def
variable
example
theorem
lemma

There is a section for each topic. Look for *** topic ***

Here we go, starting with #check.
-/

/-*** #check ***-/

/-
In Lean, the #check command is part of Lean but not part of
predicate logic. It takes any expression does two things:

(1) It checks it for syntax errors
(2) If it's syntactically correct, it tells you its type

Let's look at some examples. Hover over the blue squiggle.
-/

#check 5    -- 5 is a good expression; it's type is ℕ (natural number)
#check ℕ    -- ℕ is a data type so *it's& type is Type


/-
The type of the value 5 is ℕ
The type of ℕ is Type
Type is the type of every simple data type in Lean
-/


/-
Let's look at another example
-/

#check "Hi"   -- "Hi" is a value true of the string data type
#check string -- string is a data type so it's type is also Type


/-
The type of 5 is ℕ (5 : ℕ) and the type of ℕ is type (ℕ : Type)
The type of "Hi" is string ("Hi" : string") and the type of string is type (type : Type)
Similarly in Lean, the type of tt is bool (tt : bool) and the type of bool is Type (bool : Type)
In Lean, the type of every basic data type is just Type. Types are values, too, in Lean.
That let's us express ideas such as this: every value, t, of every data type T, equals itself
-/

#check ∀ (T : Type) (t : T), t = t
-- for every type T, and every value t of this type, t = t.


/-
Now let's look at using #check to check expressions involving propositions. 
-/

#check ∀ (P : Prop), P ∨ ¬P

/-
The expression, ∀ (P : Prop), P ∨ ¬P, is syntactically correct;
and because this value is a proposition, it's type is Prop. The 
type of any proposition our higher-order predicate logic is Prop. 
Here's another example.
-/

#check 0 = 1

/-
The expression 0 = 1 is a syntactically correct proposition,
and because it's a proposition, it's type is also Prop
-/

#check true

/-
Finally, the logical expression, true, is also a proposition,
so it's type is also Prop.
-/


/-*** def ***-/

/-
The def keyword in Lean establishes a new definition: a binding
of a variable to a value of a specified type. First, let's look
at binding names to values of a few data types.
-/

def five : ℕ := 5

/-
This definition declares five to be a variable name, to be bound
to a value of type ℕ, and in particular now bound to the value, 5.
We can now use #check to see that we've got what we expect here.
-/

#check five

/-
#check tells us that five is a correct expression and that it is
an expression of type ℕ.
-/

/-
Note that when Lean can infer the type of a variable from the 
value bound to it, you can elide the explicit "type judgment"
-/

def six := 6
#check 6
#check six



/-
Ok, now let's look at the case where we're working now with 
data values but with proofs of propositions. We'll start with
the proposition, true.
-/

def proof_of_true : true := true.intro

/-
Here we define proof_of_true to be a variable, meant to be 
bound to a "proof" (or proof value, or proof object) because 
"true" is a proposition not a data type. We then bind it to 
the proof value, true.intro, which, as you will recall, is the 
one and only proof of true in our logic. Proofs are mathematical
objects/values, just like data values.
-/

/-
It's worthwhile at this point to think hard again about types.
The type of proof_of_true in our logic is *true*. That's what
the "type judgement", (proof_of_true : true), expresses. And
of course the type of true is Prop.
-/

/-
When assigning proof values to variables, it's often beneficial
to work out the proof value a bit at a time. That's what proof
"scripts" are for. We could have written the previous example 
using a proof script just as well. 
-/

def another_proof_of_true : true := begin exact true.intro end

/-
The script, :begin exact true.intro end", results in exactly the
proof value, true.intro, which is then bound to the variable, 
another_proof_of_true.
-/

#check proof_of_true
#check another_proof_of_true
#check true


/-
There's a deep parallel in our higher-order logic between data 
values and proof values, and between data types and propositions. 
Let's make this clear by examples.

- The type of "five" is ℕ, and the type of ℕ is Type
- The type of "Hi" is string, and the type of string is Type
- The type of tt is bool (in Lean), and the type of bool is Type.

- The type of true.intro is true, and the type of true is Prop 
- The type of proof_of_true is true, and the type of true is Prop
- The type of another_proof_of_true is true, and its type is Prop
-/

/-
Here's another example
-/

def a_fact : ∀ (P Q : Prop), P ∧ Q → P :=
begin
  assume P Q h,
  exact (and.elim_left h),
end 

/-
Here we declare a_fact to be a variable that is meant to be bound
(to have as its value) of proof of ∀ (P Q : Prop), P ∧ Q → P. The
proof script produces such a "proof" value, which is then bound to
the variable a_fact. The #check command reports that the "type" of
a_fact is ∀ (P Q : Prop), P ∧ Q → P. Propositions are types in our
higher-order logic, and just as Lean type checks the values you try
to bind to variables, giving errors if the types don't match, so in
the same way Lean checks the types of proof values to be sure they
match the propositions they're intended to be proofs of!
-/

def oops : ℕ := "Hi"       -- type error (read the error message)
def argh : ∀ (P Q : Prop), P ∧ Q → P := true.intro -- type error!

/-
Please read the error messages: in both cases we have a type error.
In the first example, we try to bind a string value, "Hi,"  to a 
variable declared to be of type ℕ, and that produces a type error. 
Similarly, when we try to bind a proof value, true.intro (a proof 
of true) to the variable, argh, we get a type error, because argh
is meant to be bound to a proof of ∀ (P Q : Prop), P ∧ Q → P.
-/

/-
We can clearly distinguish the use of the #check command to check 
the syntax and type of an expression you provide, from the use of
*type checking* in Lean (as in Java), which checks whether the type
of a value being bound to a variable is the same as the type that
the variable expects.
-/

/-*** variable ***-/

/-
The variable command in Lean declares a new variable an it's type
without binding a value to it. 
-/

variable seven : ℕ 
variable some_data_type : Type
variable a_silly_proposition : ∀ (P : Prop), true

/-
You can use #check to check the types of such variables
-/

#check seven                -- it's type is nat
#check some_data_type       -- it's type is Type
#check a_silly_proposition  -- it's type is ∀ (P : Prop), true

/-
We can tell whole logical stories just using variables and their types
-/

variable Person : Type    -- Person is some data type
variable Likes : Person → Person → Prop -- Likes is a 2 argument predicate
variables (Mary Margo : Person)  -- p and q are variables of type Person
variable likes_mary_margo : Likes Mary Margo -- likes_mary_margo is a proof of Likes Mary Margo

/-
We've basically assumed that likes_mary_margo is bound to (has as its value) 
a proof of Likes Mary Margo. We can see that Lean's type checker thinks so, too.
-/
def proof_mary_likes_margo : Likes Mary Margo := likes_mary_margo -- good proof, it typechecks
def bad_proof : Likes Mary Margo := true.intro -- bad proof, type checker catches it!



/-*** example ***-/

/-
The "example" keyword specifies a type (often a proposition), and expects you 
to give a value of this type (often a proof), which it then *typechecks* for 
correctness. The only difference between example and def is that example does
not bind a given value to a variable. It typechecks it to make sure it's ok, 
and then just forgets about it. It's useful for checking that a proof is correct
without "remembering" the proof value by binding it to a variable. 
-/

def eight : ℕ := 8    -- typechecks 8 to ensure it's ℕ, binds value to "eight"
example : ℕ := 9      -- typechecks 9 to ensure it's ℕ and then forgets about it
example : ℕ := "Hi"   -- type error
example : true := true.intro -- checks that true.intro is a correct proof of true
example : ∀ (P Q : Prop), P ∧ Q → P := begin intros P Q h, exact and.elim_left h end  -- good proof
example : ∀ (P Q : Prop), P ∧ Q → P := begin intros P Q h, exact and.elim_right h end -- bad proof


/-*** theorem and lemma keywords ***-/

/-
Finally, the keywords, "theorem" and "lemma" work *just like* def. They are
preferred, however, when what you're binding to a variable is a proof value,
rather than a data value.
-/

def yet_another_proof_of_true : true := true.intro    -- using def
theorem i_get_it_true_is_true : true := true.intro    -- using theorem
lemma yeah_yeah_yeah          : true := true.intro    -- using lemma

/-
In mathematical writing, theorem is use to refer to a proof of a "big and
important proposition." A theorem is often the main result in a mathematical
presentation. Mathematicians use "lemma" to refer to a proof of a smaller
proposition that one develops on the way to proving a theorem. These words
allow Lean users to use terminology from mathematics. Just remember that
they work exactly the same as def. The only difference in Lean is that you
can't use them to bind *data* values to variables (without going through 
some extra effort that we don't need to get into here).
-/

theorem fiver : ℕ := 5    -- Read the error message. ℕ is a data type.