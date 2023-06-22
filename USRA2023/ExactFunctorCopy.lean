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
def exactOfNatIso (F : C ⥤ D) {G : C ⥤ D} [Exact F] (h : F ≅ G) : Exact G := 
  letI : PreservesFiniteLimits G := preservesFiniteLimitsOfNatIso _ h
  letI : PreservesFiniteColimits G := preservesFiniteColimitsOfNatIso _ h
  inferInstance

def exactComp {E : Type _} [Category E] 
  (F : C ⥤ D) (G : D ⥤ E) [Exact F] [Exact G] : Exact (F ⋙ G) := 
    letI : PreservesFiniteLimits (F ⋙ G) := compPreservesFiniteLimits F G
    letI : PreservesFiniteColimits (F ⋙ G) := compPreservesFiniteColimits F G
    inferInstance

class AB4 (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasCoproducts 𝓐] where
  exact (α : Type v) : Exact (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐)

instance (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasCoproducts 𝓐] [AB4 𝓐] (α : Type v) : 
  Exact (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) := AB4.exact _

class AB5 (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasColimits 𝓐] where
  exact (J : Type v) [SmallCategory J] [IsFiltered J] : Exact (colim : (J ⥤ 𝓐) ⥤ 𝓐)

noncomputable instance (𝓐 : Type _) [Category.{v} 𝓐] [Abelian 𝓐] [HasCoproducts 𝓐] (α : Type v) : 
    PreservesColimitsOfSize (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) := 
  Adjunction.leftAdjointPreservesColimits colimConstAdj

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
    dsimp only [coproductColimitCocone_pt]
    apply Sigma.hom_ext
    intros s
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, ← h {s}, 
      coproductColimitDiagram_obj, coproductColimitCocone_pt, const_obj_obj,
      coproductColimitCocone_ι_app, colimit.ι_desc_assoc, Discrete.functor_obj,
      Cofan.mk_pt, Cofan.mk_ι_app]
  }

noncomputable
def coproductIsoColimit {α : Type v} (X : α → C) [HasColimits C] : 
    ∐ X ≅ colimit (coproductColimitDiagram X) := 
  (coproductColimitCoconeIsColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

noncomputable
def coproductDiagramNatTrans {α : Type v} {X Y : α → C} (η : X ⟶ Y) [HasColimits C] :
    coproductColimitDiagram X ⟶ coproductColimitDiagram Y where
  app S := Limits.Sigma.map fun b => η b

noncomputable
def changeCoproductCocone {α : Type v} {X Y : α → C} (η : X ⟶ Y) [HasColimits C] :
    Cocone (coproductColimitDiagram X) where
  pt := colimit (coproductColimitDiagram Y)
  ι := {
    app := fun S => (coproductDiagramNatTrans η).app _ ≫ colimit.ι _ S
    naturality := fun X₁ Y₁ f => by
      apply Sigma.hom_ext
      intros b
      simp only [coproductDiagramNatTrans]
      rw [←(colimit.w (coproductColimitDiagram Y) f)]
      simp
  }

example (α : Type v) (F : Discrete α ⥤ C) [HasColimits C] : 
  (fun b => F.obj {as := b}) = F.obj ∘ Discrete.mk := rfl

noncomputable
def finsetColimitDiagram (α : Type v) [HasColimits C] : 
    (Discrete α ⥤ C) ⥤ C  where
  /- (F.obj ∘ Discrete.mk) vs (fun b => X.obj {as := b})     -/
  obj := fun F => colimit (coproductColimitDiagram (fun b => F.obj {as := b})) 
  map := fun {F G} η => colimit.desc _ (changeCoproductCocone fun b => η.app _)
  map_id := fun X => by 
    apply colimit.hom_ext
    intro j₁
    apply colimit.hom_ext
    intro b
    have h : (coproductDiagramNatTrans fun b => 𝟙 (X.obj { as := b })).app j₁ = 𝟙 _ := by {
      dsimp only [coproductColimitDiagram_obj]
      simp only [coproductDiagramNatTrans]
      ext
      simp
    }
    simp [changeCoproductCocone, h]
  map_comp := fun {X Y Z} f g => by
    simp only [changeCoproductCocone, coproductDiagramNatTrans]
    aesop_cat

noncomputable
def discreteToFinsetMap {α : Type v} [HasColimits C] {F G : Discrete α ⥤ C} (f : F ⟶ G) :
    F.obj ∘ Discrete.mk ⟶ G.obj ∘ Discrete.mk := by {have h := f.app; aesop_cat}
  
noncomputable
def discreteToFinset (α : Type v) [HasColimits C] :
    (Discrete α ⥤ C) ⥤ (Finset α ⥤ C) where
  obj := fun F => coproductColimitDiagram (F.obj ∘ Discrete.mk) 
  map := fun {F G} f => coproductDiagramNatTrans (discreteToFinsetMap f)
  map_id := fun X => by {
    ext j
    have h : (coproductDiagramNatTrans fun b => 𝟙 (X.obj { as := b })).app j = 𝟙 _ := by {
      dsimp only [coproductColimitDiagram_obj]
      simp only [coproductDiagramNatTrans]
      ext
      simp
    }
    exact h
  }
  map_comp := fun {X Y Z} f g => by {
    simp only [discreteToFinsetMap, coproductDiagramNatTrans]
    aesop_cat
  }

def exactDiscreteToFinset (α : Type v) [HasColimits C] : Exact (discreteToFinset (C := C) α) := sorry

noncomputable
def finsetColimitDiagram' (α : Type v) [HasColimits C] :
    (Finset α ⥤ C) ⥤ C := colim 

def actuallyUsefulIso (α : Type v) [HasColimits C] : 
  (colim : (Discrete α ⥤ C) ⥤ C) ≅  
  discreteToFinset α ⋙ colim := sorry

noncomputable
def coproductFunctorIsoColimit (α : Type v) [HasColimits C] :
    (colim : (Discrete α ⥤ C) ⥤ C) ≅ finsetColimitDiagram α :=
  NatIso.ofComponents (fun F => 
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))
    ≪≫ coproductIsoColimit _) 
  sorry

noncomputable instance (α : Type v) : DecidableEq α := Classical.decEq α

noncomputable
instance [Abelian C] [HasColimits C] [AB5 C] : AB4 C := by
  constructor
  intro α
  suffices Exact (discreteToFinset (C := C) α ⋙ colim) by 
    apply exactOfNatIso _ (actuallyUsefulIso α).symm
  -- letI : IsFiltered (Finset α) := inferInstance
  letI : Exact (colim : (Finset α ⥤ C) ⥤ C) := AB5.exact _
  suffices Exact (discreteToFinset (C := C) α) by
    apply exactComp  
  exact (exactDiscreteToFinset α)

end CategoryTheory.Functor