import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Tactic


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

/- Might help later? -/
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

@[simps!]
noncomputable
def coproductIsoColimit {α : Type v} (X : α → C) [HasColimits C] : 
    ∐ X ≅ colimit (coproductColimitDiagram X) := 
  (coproductColimitCoconeIsColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

/-
noncomputable
def coproductIsoColimit' {α : Type v} (X : α → C) [HasColimits C] : 
    ∐ X ≅ colimit (coproductColimitDiagram X) where
    hom := Sigma.desc fun a => 
      letI e1 : X a ⟶ ∐ (fun b : ({a} : Finset α) => X b) := 
        Sigma.ι (fun b : ({a} : Finset α) => X b) ⟨a, by simp⟩
      letI e2 : ∐ (fun b : ({a} : Finset α) => X b) ⟶ colimit (coproductColimitDiagram X) := 
        colimit.ι (coproductColimitDiagram X) {a}
      e1 ≫ e2
    inv := colimit.desc (coproductColimitDiagram X) (coproductColimitCocone X)
    inv_hom_id := by 
      ext j
      simp only [coproductColimitDiagram_obj, colimit.ι_desc_assoc, coproductColimitCocone_ι_app]
      ext jj
      simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, colimit.ι_desc]
      have leq : {↑jj} ≤ j := Iff.mpr Finset.subset_iff (fun _ x =>
       by simp [Finset.eq_of_mem_singleton x])
      rw [←(colimit.w (coproductColimitDiagram X) <| homOfLE leq)]
      simp
    hom_inv_id := by aesop_cat

example {α : Type v} (X : α → C) [HasColimits C] :
  coproductIsoColimit' X = coproductIsoColimit X := rfl
-/

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

@[simps]
noncomputable
def coproductDiagramNatTrans {α : Type v} {X Y : α → C} (η : X ⟶ Y) [HasColimits C] :
    coproductColimitDiagram X ⟶ coproductColimitDiagram Y where
  app S := Limits.Sigma.map fun b => η b

@[simps]
noncomputable
def changeCoproductCocone {α : Type v} {X Y : α → C} (η : X ⟶ Y) [HasColimits C] :
    Cocone (coproductColimitDiagram X) where
  pt := colimit (coproductColimitDiagram Y)
  ι := {
    app := fun S => (coproductDiagramNatTrans η).app _ ≫ colimit.ι _ S
    naturality := fun X₁ Y₁ f => by
      apply Sigma.hom_ext
      intro s
      simp only [coproductDiagramNatTrans]
      rw [←(colimit.w (coproductColimitDiagram Y) f)]
      simp only [const_obj_obj, coproductColimitDiagram_obj, coproductColimitDiagram_map, colimit.ι_desc_assoc,
        Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app, ι_colimMap_assoc, Discrete.natTrans_app, const_obj_map,
        Category.comp_id]
    }

@[simps]
noncomputable
def finsetColimitDiagram (α : Type v) [HasColimits C] : 
    (Discrete α ⥤ C) ⥤ C  where
  /- (F.obj ∘ Discrete.mk) vs (fun b => X.obj {as := b})     -/
  obj := fun F => colimit (coproductColimitDiagram (fun j => F.obj ⟨j⟩))
  map := fun {F G} η => colimit.desc _ (changeCoproductCocone fun b => η.app _)
  map_id := fun X => by 
    apply colimit.hom_ext
    intro j₁
    apply colimit.hom_ext
    intro b
    have h : (coproductDiagramNatTrans fun b => 𝟙 (X.obj { as := b })).app j₁ = 𝟙 _ := by
      dsimp only [coproductColimitDiagram_obj]
      simp only [coproductDiagramNatTrans]
      ext
      simp
    simp [changeCoproductCocone, h]
    erw [Category.id_comp]
  --map_comp := sorry

/-
noncomputable
def discreteToFinsetMap {α : Type v} [HasColimits C] {F G : Discrete α ⥤ C} (f : F ⟶ G) :
    F.obj ∘ Discrete.mk ⟶ G.obj ∘ Discrete.mk := --by {have h := f.app; aesop_cat}
  fun _ => f.app _
-/
  
@[simps]
noncomputable
def discreteToFinset (α : Type v) [HasColimits C] :
    (Discrete α ⥤ C) ⥤ (Finset α ⥤ C) where
  obj := fun F => coproductColimitDiagram (fun j => F.obj ⟨j⟩) --(fun b => F.obj {as := b}) --
  map := fun {F G} f => coproductDiagramNatTrans (fun j => f.app _)
  map_id := fun X => by 
    ext j
    have h : (coproductDiagramNatTrans fun b => 𝟙 (X.obj { as := b })).app j = 𝟙 _ := by 
      dsimp only [coproductColimitDiagram_obj]
      simp only [coproductDiagramNatTrans]
      ext
      simp
    exact h
  map_comp := fun {X Y Z} f g => by 
    simp only [coproductDiagramNatTrans]
    aesop_cat

-- def discreteToFinsetReflectionHom {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (F G : J ⥤ (Discrete α ⥤ C))
--   (ι : (F ⋙ discreteToFinset α) ⟶ (G ⋙ discreteToFinset α)) : F.obj i ⟶ G.obj i where
--     app :=


    


--the natural transformation we get by restricting to singletons
-- def discreteToFinsetReflectionNat {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (F G : J ⥤ (Discrete α ⥤ C))
--   (h : (F ⋙ discreteToFinset α) ⟶ (G ⋙ discreteToFinset α)) : F ⟶ G where
--     app := fun i => {
--       app := fun a => by {
--         sorry
--       }
--     }
--     naturality := sorry
  

def discreteCoconeFromFinsetCocone {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ (Discrete α ⥤ C)) 
  (s : Cocone (K ⋙ discreteToFinset α)) : Cocone K where
    pt := Discrete.functor (fun a => s.pt.obj {a})
    ι := {
      app := fun j => Discrete.natTrans (fun a => by {
        simp only [const_obj_obj]
        have h : (K.obj j).obj a ≅ ((K ⋙ discreteToFinset α).obj j).obj {a.as} := by
          sorry
        letI := (s.ι.app j).app {a.as}
        sorry
      })
          
      naturality := sorry

    }
    -- by
    --   have f : (const J).obj s.pt ⟶ (const J).obj (Discrete.functor fun a => s.pt.obj {a}) ⋙ discreteToFinset α := by {
    --     sorry
    --   }
    --   exact (discreteToFinsetReflectionNat K _ (s.ι ≫ f))


-- will be where biproducts come into play (or at least in the limit equivalent)
def discreteToFinsetOnFromFinsetCoconeIso {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ (Discrete α ⥤ C)) 
  (s : Cocone (K ⋙ discreteToFinset α)) : ((discreteToFinset (C := C) α).mapCocone (discreteCoconeFromFinsetCocone K s)).pt ≅ s.pt where
    hom := {
      app := sorry
      naturality := sorry
    }
    inv := sorry
    hom_inv_id := sorry
    inv_hom_id := sorry

      

-- def inclHom {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ (Discrete α ⥤ C)) 
--   (s : Cocone (K ⋙ discreteToFinset α)) : (discreteCoconeFromFinsetCocone K s).pt ⟶ s.pt where

noncomputable
def idk {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ (Discrete α ⥤ C))  :
  PreservesColimit K (discreteToFinset (C := C) α) where
    preserves := fun c => {
      desc := fun s => ((discreteToFinset (C := C) α).mapCoconeMorphism ({ Hom := (c.desc (discreteCoconeFromFinsetCocone K s)) })).Hom ≫ 
        (discreteToFinsetOnFromFinsetCoconeIso K s).hom
      fac := fun s j => by
        simp only [comp_obj, mapCocone_pt, const_obj_obj, mapCocone_ι_app]
        sorry
      uniq := by 
        sorry
    }

def discreteCoconeFromFinsetCone {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ (Discrete α ⥤ C)) 
  (s : Cone (K ⋙ discreteToFinset α)) : Cone K where
    pt := Discrete.functor (fun a => s.pt.obj {a})
    π := sorry

noncomputable
def idk2 {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ (Discrete α ⥤ C))  :
  PreservesLimit K (discreteToFinset (C := C) α) where
    preserves := fun c => {
      lift := sorry
      fac := fun s j => by 
        sorry
      uniq := by 
        sorry
    }

-- This will use the fact that finite products (or coproducts) in an abelian category are exact.
-- the reason is that finite (co)products are isomorphic to finite biproducts, which are both limits and colimits, and
-- thus commute with both limits and colimits.  

#check evaluation

/-

If `K : J ⥤ (C ⥤ D)`, `X : C`, then 

`(colimit K).obj X ≅ colimit (j ↦ (K.obj j).obj X)`

`K ⋙ evaluation at X : J ⥤ D`

-/

namespace preservesColimitAux

@[simps]
noncomputable
def foo {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J]
    {K : J ⥤ Discrete α ⥤ C} (T : Cocone (K ⋙ discreteToFinset α)) 
    {A : Finset α} (q : α) (hq : q ∈ A) :
    Cocone (K ⋙ (evaluation _ _).obj ⟨q⟩) where
  pt := T.pt.obj A
  ι := {
    app := fun j => Sigma.ι (fun (s : ({q} : Finset α)) => (K.obj j).obj ⟨s⟩) ⟨q, by simp⟩ ≫ 
      (T.ι.app j).app {q} ≫ T.pt.map (homOfLE <| by simpa)
    naturality := by
      intro i j f
      dsimp
      simp only [Category.comp_id]
      have Tw := T.w f
      apply_fun (fun e => e.app {q}) at Tw
      simp [← Tw]
  }

@[simps]
noncomputable
def desc {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J]
    {K : J ⥤ Discrete α ⥤ C} {E : Cocone K} (hE : IsColimit E) (T : Cocone (K ⋙ discreteToFinset α)) :
    ((discreteToFinset α).mapCocone E).pt ⟶ T.pt where
  app := fun A => Sigma.desc fun ⟨q, hq⟩ => 
    let K' := K ⋙ (evaluation _ _).obj ⟨q⟩ 
    let E' : Cocone K' := Functor.mapCocone ((evaluation _ _).obj ⟨q⟩) E
    let hE' : IsColimit E' := isColimitOfPreserves _ hE
    by exact hE'.desc (foo T q hq)
  naturality := by
    intro A B f
    dsimp 
    apply Sigma.hom_ext ; rintro ⟨a,ha⟩   
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, 
      Cofan.mk_ι_app, colimit.ι_desc]
    let E' := ((evaluation (Discrete α) C).obj { as := a }).mapCocone E
    let hE' : IsColimit E' := (isColimitOfPreserves ((evaluation (Discrete α) C).obj { as := a }) hE)
    apply hE'.hom_ext
    intro j
    simp only [hE'.fac, hE'.fac_assoc]
    simp only [comp_obj, evaluation_obj_obj, foo_pt, foo_ι_app, const_obj_obj, discreteToFinset_obj, Category.assoc]
    simp only [comp_obj, evaluation_obj_obj, Category.assoc, ← T.pt.map_comp]
    rfl

end preservesColimitAux

noncomputable
def preservesColimitsOfFiniteShapeDiscreteToFinset (α : Type v) [HasColimits C] 
    (J : Type) [SmallCategory J] [FinCategory J] : 
  PreservesColimitsOfShape J (discreteToFinset (C := C) α) where
    preservesColimit {K} := {
      preserves := fun {E} hE => {
        desc := fun T => preservesColimitAux.desc _ _
        fac := by
          intro S j
          ext A
          simp only [comp_obj, discreteToFinset_obj, coproductColimitDiagram_obj, mapCocone_pt, const_obj_obj,
            mapCocone_ι_app, discreteToFinset_map, id_eq, evaluation_obj_obj, Finset.le_eq_subset, eq_mpr_eq_cast,
            comp_map, evaluation_obj_map, const_obj_map, Discrete.functor_obj, Discrete.natTrans_app, NatTrans.comp_app,
            coproductDiagramNatTrans_app, Eq.ndrec, colimit.map_desc]
          apply colimit.hom_ext
          rintro ⟨a,ha⟩ 
          simp only [Discrete.functor_obj, preservesColimitAux.desc_app, id_eq, comp_obj, evaluation_obj_obj,
            const_obj_obj, discreteToFinset_obj, coproductColimitDiagram_obj, colimit.map_desc, colimit.ι_desc,
            Cocones.precompose_obj_pt, Cofan.mk_pt, Cocones.precompose_obj_ι, NatTrans.comp_app, Discrete.natTrans_app,
            Cofan.mk_ι_app]
          dsimp only [Discrete.functor_obj, Cocones.precompose_obj_pt, Cofan.mk_pt, Cocones.precompose_obj_ι,
            NatTrans.comp_app, const_obj_obj, Discrete.natTrans_app, Cofan.mk_ι_app]
          let E' := ((evaluation (Discrete α) C).obj { as := a }).mapCocone E
          let hE' : IsColimit E' := (isColimitOfPreserves ((evaluation (Discrete α) C).obj { as := a }) hE)
          change E'.ι.app _ ≫ _ = _
          rw [hE'.fac]
          simp only [comp_obj, evaluation_obj_obj]
          simp only [preservesColimitAux.foo_pt, preservesColimitAux.foo_ι_app, comp_obj, evaluation_obj_obj,
            const_obj_obj, discreteToFinset_obj]
          rw [← NatTrans.naturality, ← Category.assoc]
          congr 1
          simp
        uniq := by
          intro S m hm
          ext A
          dsimp
          apply Sigma.hom_ext
          rintro ⟨a,ha⟩ 
          simp only [colimit.ι_desc]
          dsimp
          let E' := ((evaluation (Discrete α) C).obj { as := a }).mapCocone E
          let hE' : IsColimit E' := (isColimitOfPreserves ((evaluation (Discrete α) C).obj { as := a }) hE)
          apply hE'.hom_ext ; intro j
          rw [hE'.fac]
          dsimp
          specialize hm j
          apply_fun (fun e => e.app {a}) at hm
          dsimp at hm
          rw [← hm]
          simp only [Category.assoc, ι_colimMap_assoc, Discrete.functor_obj, Discrete.natTrans_app]
          congr 1
          rw [← NatTrans.naturality, ← Category.assoc]
          congr 1
          simp
      }
    }

noncomputable
def preservesLimitsOfFiniteShapeDiscreteToFinset (α : Type v) [HasColimits C] (J : Type) [SmallCategory J] [FinCategory J] : 
  PreservesLimitsOfShape J (discreteToFinset (C := C) α) where
    preservesLimit := idk2 _

-- instance (α : Type v) [HasCoLimits C] : PreservesFiniteLimits (discreteToFinset (C := C) α) := sorry


noncomputable
def rightExactDiscreteToFinset (α : Type v) [HasColimits C] : PreservesFiniteColimits (discreteToFinset (C := C) α) where
  preservesFiniteColimits := fun J => preservesColimitsOfFiniteShapeDiscreteToFinset _ J

noncomputable
def leftExactDiscreteToFinset (α : Type v) [HasColimits C] : PreservesFiniteLimits (discreteToFinset (C := C) α) where
  preservesFiniteLimits := fun J => preservesLimitsOfFiniteShapeDiscreteToFinset _ J

def exactDiscreteToFinset (α : Type v) [HasColimits C] : Exact (discreteToFinset (C := C) α) := 
  sorry

noncomputable
def finsetColimitDiagram' (α : Type v) [HasColimits C] :
    (Finset α ⥤ C) ⥤ C := colim 

noncomputable
def coproductFunctorIsoColimit (α : Type v) [HasColimits C] :
    (colim : (Discrete α ⥤ C) ⥤ C) ≅ finsetColimitDiagram α :=
  NatIso.ofComponents (fun F => 
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))
    ≪≫ coproductIsoColimit _) <| by
  rintro ⟨x⟩ ⟨y⟩ f
  apply colimit.hom_ext
  rintro ⟨j⟩ 
  dsimp [Function.comp]
  simp

noncomputable
def actuallyUsefulIso (α : Type v) [HasColimits C] : 
    (colim : (Discrete α ⥤ C) ⥤ C) ≅  
    discreteToFinset α ⋙ colim := 
  coproductFunctorIsoColimit α 

--noncomputable
--def exactDiscreteToFinset' (α : Type v) [HasColimits C] : Exact (discreteToFinset (C := C) α) := sorry

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