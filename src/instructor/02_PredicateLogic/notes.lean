-- IGNORE THIS FILE PLEASE


/-
As a test of your understanding of what was just said, does it make
sense to you that if you have a predicate with zero parameters, that's 
a proposition? How about this: if you've got a predicate with, say, 
found arguments/parameters, and you fix the value of one of these
parameters to a specific actual value of the right type, the result
is a still predicate, but now with one less, now three remaining
parameters? That is true. 

The way we represent a predicate with one argument of some type, T,
is as an object, a predicate, P, of type T → Prop. KEY IDEA: Look 
back at → elimination. It says that if you have a "proof object" 
of T → Prop, and you have an object, t, of type T, then you can
derive something of type Prop: a proposition! In other words, you
can *use* a predicate, P : T → Prop if you also happen have or if
you can acquire an object (t : T). 

MAKE SURE YOU SEE THIS POINT. IF YOU DON'T FIND PEOPLE WITH WHOM
YOU CAN TALK IT THROUGH. GO ON PIAZZA IS GOOD ADVICE.

Ok, so from now on, when you see anything that looks like T → Prop,
you think, "Ok, that's just a predicate, a proposition with a blank,
where the blank can be filled in by any object of type T, whatever
that type might be." This formulation works for all types. Example:
Suppose T is Person. Then (isNice : T → Prop) is a predicate that
takes a person, let's call them p, as an argument, and "reduces to"
the proposition, (isNice p). In English we'd just say, "p is nice."

Finally, a crucial point: we can represent *properties* of things
as predicates. A property of an object is a characteristic that it
as an individual possesses. As an example, think of the universe 
of all balls used in sports: all those individual balls. Now think
of a property that some of those balls have: in particular consider
the property of being blue. Some balls have this property, some
doon't. Or in the realm of intengers, some have the peropty of
being even, or prime, or beautiful, and some don't. 

Let's take a property over the integers, specifically the property
of being even. We will represent this property as a predicate, call
it isEven : ℤ → Prop. (ℤ is the symbol most mathenaticians use to
represent the integers.) isEven is thus some property of natural
numbers in the following sense: given any integer, n, (isEven n) is
a *proposition* that we interpret as asserting that n is even. To
be concrete, (isEven 3) we interpret as the proposition that three
is even. Under our ordinary definitions of these terms,, it's false,
but still a perfectly good proposition. On the other hand, isEven 4,
we be a proposition one for which we can construct a proof. The set
of all numbers *for which its proposition is true* is the set of 
objects that we say "has the property" that the predicate "tests
for." A property in a sense is a specific subject of objects of a
given type, namely all those that *satisfy* the constraint that
the predicate defines: of being even, prime, beautiful, or whaever.
-/
