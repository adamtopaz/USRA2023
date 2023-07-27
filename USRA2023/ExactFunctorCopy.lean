import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Tactic

import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.CompleteLattice


namespace CategoryTheory.Functor

open CategoryTheory Limits

/- Biproduct Section: I didn't know how to import the other file given -/

noncomputable
abbrev Sigma.isoBiproduct {C : Type _} [Category C] {α : Type _} 
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X]: 
    ∐ X ≅ ⨁ X := 
  colimit.isColimit _ |>.coconePointUniqueUpToIso (biproduct.isColimit _)

noncomputable
abbrev Sigma.lift {C : Type _} [Category C] {α : Type _} 
  {X : α → C} [HasZeroMorphisms C] [HasBiproduct X] {P : C} (p : ∀ (a : α), P ⟶ X a) :
    P ⟶ ∐ X := 
  biproduct.lift p ≫ (Sigma.isoBiproduct _).inv

noncomputable
def Sigma.π {C : Type _} [Category C] {α : Type _} 
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X] (a : α) : ∐ X ⟶ X a := 
  (Sigma.isoBiproduct _).hom ≫ biproduct.π _ _ 

lemma Sigma.ι_π {C : Type _} [Category C] [HasZeroMorphisms C] {α : Type _} (X : α → C) (a : α) [HasBiproduct X] :
  Sigma.ι X a ≫ Sigma.π X a = 𝟙 _ 
    := by {dsimp only [Sigma.π] ; simp}

@[reassoc (attr := simp)]
lemma Sigma.lift_π {C : Type _} [Category C] {α : Type _} 
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X] {Z : C} (f : (a : α) → (Z ⟶ X a)) (a) :
   Sigma.lift f ≫ Sigma.π _ a = f _ := by simp [Sigma.lift, Sigma.π]

lemma Sigma.hom_ext' {C : Type _} [Category C] {α : Type _} 
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X] {Z : C} (f g : Z ⟶ ∐ X) 
  (h : ∀ a, f ≫ Sigma.π _ a = g ≫ Sigma.π _ a) : f = g := by
    rw [← cancel_mono (Sigma.isoBiproduct _).hom] 
    apply biproduct.hom_ext
    intro j
    simpa using h j

/-END OF BIPRODUCT SECTION -/

variable {C : Type _} [Category C] {D : Type _} [Category D]

instance [Category C] [Abelian C] : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts

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

  
@[simps]
noncomputable
def discreteToFinset (α : Type v) [HasColimits C] :
    (Discrete α ⥤ C) ⥤ (Finset α ⥤ C) where
  obj := fun F => coproductColimitDiagram (fun j => F.obj ⟨j⟩) 
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


namespace preservesLimitAux

@[simps]
noncomputable
def foo'' {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] [HasZeroMorphisms C]
    [HasFiniteBiproducts C]
    {K : J ⥤ Discrete α ⥤ C} (T : Cone (K ⋙ discreteToFinset α)) 
    {A : Finset α} (q : α) (hq : q ∈ A) :
    Cone (K ⋙ (evaluation _ _).obj ⟨q⟩) where
  pt := T.pt.obj A
  π := {
    app := sorry --fun j => (T.π.app j).app A ≫ Sigma.π.app (fun s : A => (K.obj j).obj ⟨s⟩) ⟨q, hq⟩
    naturality := sorry
      -- fun i j f => by 
      -- simp only [Category.comp_id]
      -- have Tw := T.w f
      -- apply_fun (fun e => e.app A) at Tw
      -- simp [← Tw, Sigma.π]
      -- congr 1
      -- apply Sigma.hom_ext ; intro b
      -- letI : DecidableEq {x // x ∈ A} := Classical.decEq { x // x ∈ A }
      -- have := biproduct.ι_π (fun s : {x // x ∈ A} => (K.obj i).obj { as := ↑s }) b ⟨q, hq⟩
      -- aesop_cat -- wasn't sure how to manipulate the previous line to close the goal, so I just used aesop_cat
  }


@[simps]
noncomputable
def desc' {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] {K : J ⥤ Discrete α ⥤ C} {E : Cone K} (hE : IsLimit E)
    (T : Cone (K ⋙ discreteToFinset α)) : T.pt ⟶ ((discreteToFinset α).mapCone E).pt where
  app := fun A =>
    let f := fun q : A => E.pt.obj (Discrete.mk q)
    let g := (biproduct.isoCoproduct f).hom
    let h : ∀ q, T.pt.obj A ⟶ f q := by
      intro q
      let hq : ↑q ∈ A := by simp
      let K' := K ⋙ (evaluation _ _).obj ⟨q⟩
      let E' : Cone K' := Functor.mapCone ((evaluation _ _).obj ⟨q⟩) E
      let hE' : IsLimit E' := sorry--isLimitOfPreserves _ hE
      exact hE'.lift (foo'' T q hq)
    let γ := biproduct.lift h
    by exact (γ ≫ g)
  naturality := by
    intro A B f
    simp only [mapCone_pt, discreteToFinset_obj, coproductColimitDiagram_obj, biproduct.isoCoproduct_hom,
      coproductColimitDiagram_map, Category.assoc]
    -- apply Sigma.hom_ext ; rintro ⟨a,ha⟩   
    -- simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, 
    --   Cofan.mk_ι_app, colimit.ι_desc]
    -- let E' := ((evaluation (Discrete α) C).obj { as := a }).mapCocone E
    -- let hE' : IsColimit E' := (isColimitOfPreserves ((evaluation (Discrete α) C).obj { as := a }) hE)
    -- apply hE'.hom_ext
    -- intro j
    -- simp only [hE'.fac, hE'.fac_assoc]
    -- simp only [comp_obj, evaluation_obj_obj, foo_pt, foo_ι_app, const_obj_obj, discreteToFinset_obj, Category.assoc]
    -- simp only [comp_obj, evaluation_obj_obj, Category.assoc, ← T.pt.map_comp]
    -- rfl
    sorry

end preservesLimitAux

namespace preservesColimitAux

@[simps]
noncomputable
def foo {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J]
    {K : J ⥤ Discrete α ⥤ C} (T : Cocone (K ⋙ discreteToFinset α)) 
    {A : Finset α} (q : α) (hq : q ∈ A) :
    Cocone (K ⋙ (evaluation _ _).obj ⟨q⟩) where
  pt := T.pt.obj A
  ι := {
    app := fun j => Sigma.ι (fun (s : A) => (K.obj j).obj ⟨s⟩) ⟨q,hq⟩ ≫ (T.ι.app j).app A 
      --Sigma.ι (fun (s : ({q} : Finset α)) => (K.obj j).obj ⟨s⟩) ⟨q, by simp⟩ ≫ 
      --(T.ι.app j).app {q} ≫ T.pt.map (homOfLE <| by simpa)
    naturality := fun i j f => by
      simp only [Category.comp_id]
      have Tw := T.w f
      apply_fun (fun e => e.app A) at Tw
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
    rw [← NatTrans.naturality]
    dsimp [coproductColimitDiagramMap]
    simp
    

end preservesColimitAux

noncomputable
instance preservesColimitsOfShapeDiscreteToFinset (α : Type v) [HasColimits C] 
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
          apply_fun (fun e => e.app A) at hm
          dsimp at hm
          rw [← hm]
          simp only [Category.assoc, ι_colimMap_assoc, Discrete.functor_obj, Discrete.natTrans_app]
      }
    }

namespace preservesLimitAux

@[simps]
noncomputable
def foo' {α : Type v} [HasColimits C] {J : Type} [SmallCategory J] [FinCategory J] [HasZeroMorphisms C]
    [HasFiniteBiproducts C]
    {K : J ⥤ Discrete α ⥤ C} (T : Cone (K ⋙ discreteToFinset α)) 
    {A : Finset α} (q : α) (hq : q ∈ A) :
    Cone (K ⋙ (evaluation _ _).obj ⟨q⟩) where
  pt := T.pt.obj A
  π := {
    app := fun j => (T.π.app j).app A ≫ Sigma.π (fun s : A => (K.obj j).obj ⟨s⟩) ⟨q, hq⟩
    naturality := fun i j f => by 
      simp only [Category.comp_id]
      have Tw := T.w f
      apply_fun (fun e => e.app A) at Tw
      simp [← Tw, Sigma.π]
      congr 1
      apply Sigma.hom_ext ; intro b
      --letI : DecidableEq {x // x ∈ A} := Classical.decEq { x // x ∈ A }
      classical
      --have := biproduct.ι_π (fun s : {x // x ∈ A} => (K.obj i).obj { as := ↑s }) b ⟨q, hq⟩
      simp [biproduct.ι_π, biproduct.ι_π_assoc]
      split_ifs with h 
      · subst h ; simp
      · simp
  }

@[simps]
noncomputable
def lift {α : Type v} [HasColimits C] 
    [HasFiniteLimits C] [HasZeroMorphisms C] [HasFiniteBiproducts C] 
    {J : Type} [SmallCategory J] [FinCategory J]
    {K : J ⥤ Discrete α ⥤ C} {E : Cone K} (hE : IsLimit E) (T : Cone (K ⋙ discreteToFinset α)) :
     T.pt ⟶ ((discreteToFinset α).mapCone E).pt where
  app := fun A => Sigma.lift fun ⟨q, hq ⟩ => 
    let K' := K ⋙ (evaluation _ _).obj ⟨q⟩ 
    let E' : Cone K' := Functor.mapCone ((evaluation _ _).obj ⟨q⟩) E
    let hE' : IsLimit E' := isLimitOfPreserves _ hE
    by exact hE'.lift (foo' T q hq)
  naturality := fun i j f => by 
    dsimp
    apply Sigma.hom_ext' ; rintro ⟨a, ha⟩
    let E' := ((evaluation (Discrete α) C).obj { as := a }).mapCone E
    let hE' : IsLimit E' := (isLimitOfPreserves ((evaluation (Discrete α) C).obj { as := a }) hE)
    apply hE'.hom_ext
    intro jj
    simp only [hE'.fac, hE'.fac_assoc, Sigma.π, comp_obj, evaluation_obj_obj, mapCone_pt, mapCone_π_app, evaluation_obj_map, Category.assoc,
      biproduct.isoCoproduct_hom, coproductColimitDiagramMap, Iso.inv_hom_id_assoc, biproduct.lift_π_assoc,
      Iso.inv_hom_id_assoc, biproduct.lift_π_assoc, isLimitOfPreserves]
    dsimp [Sigma.isoBiproduct, IsColimit.coconePointUniqueUpToIso]
    have := (PreservesLimit.preserves hE).fac (foo' T a ha) jj
    dsimp at this
    rw [this]
    simp [coproductColimitDiagramMap]
    sorry

end preservesLimitAux

noncomputable
instance preservesLimitsOfShapeDiscreteToFinset (α : Type v) [Abelian C] [HasColimits C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
  (J : Type) [SmallCategory J] [FinCategory J] : 
  PreservesLimitsOfShape J (discreteToFinset (C := C) α) where
    preservesLimit {K} := {
      preserves := fun E {hE} => {
        lift := fun T => preservesLimitAux.lift hE T
        fac := sorry
        uniq := sorry
      }
    }

#check biproduct.lift

noncomputable
def exactDiscreteToFinset (α : Type v) [HasColimits C] [Abelian C] 
  : Exact (discreteToFinset (C := C) α) where 
      preservesFiniteLimits := fun _ => inferInstance
      preservesFiniteColimits := fun _ => inferInstance

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

noncomputable instance (α : Type v) : DecidableEq α := Classical.decEq α

noncomputable
instance [Abelian C] [HasColimits C] [AB5 C] : AB4 C := by
  constructor
  intro α
  suffices Exact (discreteToFinset (C := C) α ⋙ colim) by 
    apply exactOfNatIso _ (actuallyUsefulIso α).symm
  letI : Exact (colim : (Finset α ⥤ C) ⥤ C) := AB5.exact _
  suffices Exact (discreteToFinset (C := C) α) by
    apply exactComp  
  exact (exactDiscreteToFinset α)

end CategoryTheory.Functor