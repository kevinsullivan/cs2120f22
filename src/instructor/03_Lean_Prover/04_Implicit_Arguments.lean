-- UNDER CONSTRUCTION, IGNORE THIS FILE FOR NOW


/-
For example, if a function, f, takes a type, T, as its 
first argument, and a value, t, of that type, as its
second argument, then by default you would apply this
function to actual argument values with expressions 
such (f nat 4), or (f string "Hi!"). 

But why should you have to write out "nat" when Lean
knows from 4 that nat is all it can be? Good news: if
you specify the argument as implicit, then it will be
inferred, and if Lean can't infer it it will tell you.
-/

def identity1 : ∀ (T : Type) (t : T), T := 
begin
assume T t,
exact t,
end 

#eval identity1 nat 1 
#eval identity1 string "Hi!"

  /-
 This pair of examples is really very cool, as 
 it illustrates what in computer science we call
 parametric polymorphism. That means that you 
 specify a type as a parameter and then values
 of the given types as additional arguments,
and what this gives you is a whole family of
functions, here one for each type you might pass
as the actual value of the first parameter. 
And, here's the real key idea: the "code" is the
same no matter the value of the type parameter. 
Parametric polymorphism.

Try it out. Use #eval

as nat, bool, string, 0 = 0, etc) you might 
pass as the first argument, the "type " 
  -/

/-=
  arguments that are to 
be inferred from context rather than specified explicitly. When
you #check a type, it prints implicit arguments as numbered
"meta-variables." To make Lean print the type making all of
the arguments explicit, you can use @.
-/


def example1A {T : Type} (t : T) := t
def example1B {T : Type} := T → T := t

/-
When we specify arguments of a function or predicate, we can
declare them as named arguments (just in in Java or Python)m
before the colon. We can then continue the argument list after
the colon using arrown notation. 
function 
-/
