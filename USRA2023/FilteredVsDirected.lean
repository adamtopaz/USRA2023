import Mathlib.CategoryTheory.Filtered
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Directed
import Mathlib.Tactic

open CategoryTheory Limits

-- Exercise
example (L : Type u) [PartialOrder L] [IsDirected L (· ≤ ·)] : 
    IsFilteredOrEmpty L where
  cocone_objs X Y := 
    let ⟨Z,h1,h2⟩ := IsDirected.directed X Y (r := (· ≤ ·))
    ⟨Z, homOfLE h1, homOfLE h2, trivial⟩
  cocone_maps _ Y _ _ := ⟨Y, 𝟙 _, by simp⟩

example (L : Type u) [PartialOrder L] [IsDirected L (· ≤ ·)] [Nonempty L] : IsFiltered L where