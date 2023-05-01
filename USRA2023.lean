import Mathlib.Algebra.Category.GroupCat.Basic

example (G : GroupCat) (a b c : G) : a * b * c = a * (b * c) := 
  mul_assoc a b c