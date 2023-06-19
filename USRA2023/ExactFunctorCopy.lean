import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits


namespace CategoryTheory.Functor

open CategoryTheory Limits

variable {C : Type _} [Category C] {D : Type _} [Category D]

/-- TODO-/
class Exact (F : C ⥤ D) extends PreservesFiniteLimits F, PreservesFiniteColimits F

instance (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : Exact F where

example (F : C ⥤ D) [Exact F] : PreservesFiniteLimits F := inferInstance
example (F : C ⥤ D) [Exact F] : PreservesFiniteColimits F := inferInstance

/-- TODO-/
def preservesFiniteLimitsOfNatIso (F : C ⥤ D) {G : C ⥤ D} [PreservesFiniteLimits F] (h : F ≅ G) :
  PreservesFiniteLimits G where preservesFiniteLimits _ := ⟨preservesLimitOfNatIso _ h⟩

/-- TODO-/
def preservesFiniteColimitsOfNatIso (F : C ⥤ D) {G : C ⥤ D} [PreservesFiniteColimits F] (h : F ≅ G) : 
  PreservesFiniteColimits G where preservesFiniteColimits _ := ⟨preservesColimitOfNatIso _ h⟩    

/-- TODO-/
def preservesExactOfNatIso (F : C ⥤ D) {G : C ⥤ D} [Exact F] (h : F ≅ G) : Exact G := 
  letI : PreservesFiniteLimits G := preservesFiniteLimitsOfNatIso _ h
  letI : PreservesFiniteColimits G := preservesFiniteColimitsOfNatIso _ h
  inferInstance

class AB4 (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasCoproducts 𝓐] where
  exact (α : Type v) : Exact (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐)

instance (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasCoproducts 𝓐] [AB4 𝓐] (α : Type v) : 
  Exact (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) := AB4.exact _

class AB5 (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasColimits 𝓐] where
  exact (J : Type v) [SmallCategory J] [IsFiltered J] : Exact (colim : (J ⥤ 𝓐) ⥤ 𝓐)

/- Might help later? -/
noncomputable instance (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasCoproducts 𝓐] (α : Type v)
: PreservesColimitsOfSize (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) := Adjunction.leftAdjointPreservesColimits colimConstAdj

variable {C : Type _} [Category.{v} C] 

example (α : Type _) (S : Set α) (a : α) (ha : a ∈ S) : S :=
  ⟨_, ha⟩

noncomputable abbrev coproductColimitDiagramMap {α : Type v} (X : α → C)
    [HasFiniteCoproducts C] {S T : Finset α} (h : S ≤ T) : 
    ∐ (fun s : S => X s) ⟶ ∐ (fun t : T => X t) := 
  Sigma.desc fun s => Sigma.ι (fun t : T => X t) ⟨s.1, h s.2⟩ 

@[simps]
noncomputable
def coproductColimitDiagram {α : Type v} (X : α → C)
    [HasFiniteCoproducts C] : Finset α ⥤ C where
  obj S := ∐ (fun s : S => X s)
  map {S T : Finset α} (i : S ⟶ T) := coproductColimitDiagramMap X i.le

@[simps]
noncomputable
def coproductColimitCocone {α : Type v} (X : α → C) [HasColimits C] : 
    Cocone (coproductColimitDiagram X) where
  pt := ∐ X
  ι := {
    app := fun S => show ∐ (fun s : S => X s) ⟶ ∐ X from 
      Sigma.desc fun i => Sigma.ι _ i.1 }

-- def coproductCoconeFun {α : Type v} (X : α → C) [HasColimits C] (c : Cocone (coproductColimitDiagram X)) : 
--   Cocone (Discrete.functor X) where
--   pt := c.pt
--   ι := {
--     app := fun I => by {
--       intro a

--     }
--   }

@[simps]
noncomputable
def coproductColimitCoconeIsColimit {α : Type v} (X : α → C) [HasColimits C] : 
    IsColimit (coproductColimitCocone X) where
  desc S := Sigma.desc fun a => 
    letI e1 : X a ⟶ ∐ (fun b : ({a} : Finset α) => X b) := 
      Sigma.ι (fun b : ({a} : Finset α) => X b) ⟨a, by simp⟩
    letI e2 : ∐ (fun b : ({a} : Finset α) => X b) ⟶ S.pt := S.ι.app {a}
    e1 ≫ e2
  fac := fun c S => by
    dsimp only [coproductColimitDiagram_obj, coproductColimitCocone_pt, 
      const_obj_obj, coproductColimitCocone_ι_app]
    apply Sigma.hom_ext
    rintro ⟨b,hb⟩   
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, 
      Cofan.mk_ι_app, colimit.ι_desc]
    let e : ({b} : Finset α) ⟶ S := homOfLE (by simpa using hb)
    rw [← c.w e, ← Category.assoc] ; congr
    simp
  uniq :=  fun c σ h => by {
    simp only [coproductColimitCocone_pt]
    apply Sigma.hom_ext
    intros s
    specialize h {↑s}
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    rw [← h]
    simp only [coproductColimitDiagram_obj, coproductColimitCocone_pt, const_obj_obj,
      coproductColimitCocone_ι_app, colimit.ι_desc_assoc, Discrete.functor_obj,
      Cofan.mk_pt, Cofan.mk_ι_app]
  }

noncomputable
def coproductIsoColimit {α : Type v} (X : α → C) [HasColimits C] : 
    ∐ X ≅ colimit (coproductColimitDiagram X) := 
  (coproductColimitCoconeIsColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

-- noncomputable
-- def coproductIsoColimit {α : Type v} (X : α → C) [HasColimits C] : 
--     ∐ X ≅ colimit (coproductColimitDiagram X) where
--     hom := Sigma.desc fun a => 
--       letI e1 : X a ⟶ ∐ (fun b : ({a} : Finset α) => X b) := 
--         Sigma.ι (fun b : ({a} : Finset α) => X b) ⟨a, by simp⟩
--       letI e2 : ∐ (fun b : ({a} : Finset α) => X b) ⟶ colimit (coproductColimitDiagram X) := 
--         colimit.ι (coproductColimitDiagram X) {a}
--       e1 ≫ e2
--     inv := colimit.desc (coproductColimitDiagram X) (coproductColimitCocone X)
--     inv_hom_id := by 
--       ext j; simp
--       ext jj; simp
--       have leq : {↑jj} ≤ j := Iff.mpr Finset.subset_iff (fun _ x =>
--        by simp [Finset.eq_of_mem_singleton x])
--       rw [←(colimit.w (coproductColimitDiagram X) <| homOfLE leq)]
--       simp
--     hom_inv_id := by aesop_cat

instance (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasColimits 𝓐] [AB5 𝓐] : AB4 𝓐 := by
  constructor
  intro α
  haveI : PreservesFiniteColimits (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) 
    := {preservesFiniteColimits := fun J => PreservesFiniteColimits.preservesFiniteColimits J}
  sorry


end CategoryTheory.Functor