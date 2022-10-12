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

