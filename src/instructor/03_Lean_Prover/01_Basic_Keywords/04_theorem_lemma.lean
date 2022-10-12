/-*** theorem and lemma keywords ***-/

/-
The keywords, "theorem" and "lemma" work *just like* def. They are
preferred when what you're binding to a variable is a proof value,
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