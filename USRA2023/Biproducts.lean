import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

namespace CategoryTheory.Limits

open CategoryTheory

variable {C : Type _} [Category C] {α : Type _} (X : α → C) [HasZeroMorphisms C] [HasBiproduct X]

noncomputable
abbrev Sigma.isoBiproduct : 
    ∐ X ≅ ⨁ X := 
  colimit.isColimit _ |>.coconePointUniqueUpToIso (biproduct.isColimit _)

noncomputable
def Sigma.lift {Z : C} (f : (a : α) → (Z ⟶ X a)) :
    Z ⟶ ∐ X := 
  biproduct.lift f ≫ (Sigma.isoBiproduct _).inv

noncomputable
def Sigma.π (a : α) : ∐ X ⟶ X a := 
  (Sigma.isoBiproduct _).hom ≫ biproduct.π _ _ 

@[reassoc (attr := simp)]
lemma Sigma.lift_π {Z : C} (f : (a : α) → (Z ⟶ X a)) (a) :
  Sigma.lift X f ≫ Sigma.π _ a = f _ := by simp [Sigma.lift, Sigma.π]

lemma Sigma.hom_ext' {Z : C} (f g : Z ⟶ ∐ X) (h : ∀ a, f ≫ Sigma.π _ a = g ≫ Sigma.π _ a) : f = g := by
  rw [← cancel_mono (Sigma.isoBiproduct _).hom] 
  apply biproduct.hom_ext
  intro j
  simpa using h j

end CategoryTheory.Limits
