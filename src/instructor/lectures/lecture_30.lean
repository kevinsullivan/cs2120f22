/- LISTS
-/

namespace hidden 

inductive list (α : Type) : Type 
| nil : list
| cons (h : α) (t : list) : list

end hidden