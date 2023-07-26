import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.CategoryTheory.Limits.Types

open CategoryTheory Limits

example : GroupCat.{u} ⥤ Type u := forget GroupCat

namespace GroupCat

variable {J : Type u} [SmallCategory J] (F : J ⥤ GroupCat.{u})

@[ext]
lemma hom_ext {G H : GroupCat} (f₁ f₂ : G ⟶ H) 
    (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ := by 
  let g₁ : G →* H := f₁
  let g₂ : G →* H := f₂
  show g₁ = g₂
  exact MonoidHom.ext h

@[simps]
def limitConePt : Subgroup ((j : J) → F.obj j) where
  carrier := { g : (j : J) → F.obj j | ∀ (i j : J) (f : i ⟶ j), (F.map f) (g i) = g j }
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb i j f => by dsimp at * ; simp [ha,hb]
  inv_mem' := fun {a} ha i j f => by
    dsimp at *
    rw [← ha i j f]
    let ff : F.obj i →* F.obj j := F.map f
    exact ff.map_inv _

@[simps]
def limitCone : Cone F where
  pt := GroupCat.of <| limitConePt F
  π := {
    app := fun j => 
      show (limitConePt F) →* F.obj j from
      MonoidHom.comp (Pi.evalMonoidHom _ j) (limitConePt F).subtype
    naturality := by 
      intro i j f 
      dsimp
      simp only [Category.id_comp]
      apply MonoidHom.ext
      rintro ⟨x,hx⟩
      apply (hx i j f).symm }

def isLimitLimitCone : IsLimit (limitCone F) where
  lift := fun E => 
    show E.pt →* (limitCone F).pt from { 
      toFun := fun e => ⟨Pi.monoidHom (fun j => E.π.app j) e, by
        intro i j f   
        dsimp
        have := E.w f
        apply_fun (fun t => t e) at this
        exact this ⟩
      map_one' := by
        apply Subtype.ext
        funext
        simp only [Pi.monoidHom_apply, map_one]
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        funext
        dsimp
        simp only [map_mul] } 
  fac := by 
    intro E j
    ext
    rfl
  uniq := by
    intro E m hm
    ext e 
    apply Subtype.ext
    funext j
    dsimp
    specialize hm j
    apply_fun (fun t => t e) at hm
    exact hm

noncomputable
example : PreservesLimits (forget GroupCat) := by
  constructor
  intro J _
  constructor
  intro G
  apply preservesLimitOfPreservesLimitCone (isLimitLimitCone G)
  have := Types.limitCone.{u,u} (G ⋙ forget _)
  have := Types.limitConeIsLimit.{u,u} (G ⋙ forget _)
  apply this

end GroupCat