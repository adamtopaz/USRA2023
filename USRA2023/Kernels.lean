import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Preadditive.LeftExact

open CategoryTheory Limits

variable {C : Type u} {D : Type v} [Category.{v} C] [Category.{v} D]
variable (F : C ⥤ D) [PreservesFiniteLimits F]
variable [Abelian C] [Abelian D] [Functor.Additive F]

noncomputable def kernelIso {X Y : C} (f : X ⟶ Y) : 
    F.obj (kernel f) ≅ kernel (F.map f) := 
  PreservesKernel.iso F f

def kernelIso_hom_comp_ι {X Y : C} (f : X ⟶ Y) :
    (kernelIso F f).hom ≫ kernel.ι _ = F.map (kernel.ι _) := 
  by simp [kernelIso]

def kernelIso_inv_comp_ι {X Y : C} (f : X ⟶ Y) :
    (kernelIso F f).inv ≫ F.map (kernel.ι _) = kernel.ι _ := 
  by simp [kernelIso, Iso.inv_comp_eq]

/-
Exercise: Repeat the above for cokernels instead of kernels.
You will need to replace `F` with a functor which preserves finite *colimits*.
-/


/-
The following three are a bit more challenging!
-/

/-
X - f - > Y - g - > Z

e : A -> B
i : K -> A

Exact i e
Exact (0 : 0 ⟶ K) i <-> i being a mono

-/
open ZeroObject Pseudoelement

noncomputable
def isoKernel_of_exact {K A B : C} {f : A ⟶ B} {i : K ⟶ A} 
  (h1 : Exact i f) (h2 : Exact (0 : 0 ⟶ K) i) : K ≅ kernel f :=
  let e : K ⟶ kernel f := kernel.lift f i h1.w
  haveI : Epi e := Exact.epi_kernel_lift h1
  haveI : Mono i := by rwa [mono_iff_exact_zero_left]
  haveI : Mono e := by
    constructor
    intro Z a b h
    rw [← cancel_mono (kernel.ι f)] at h
    simp only [Category.assoc, kernel.lift_ι, zero_comp] at h
    rwa [cancel_mono i] at h
  haveI : IsIso e := isIso_of_mono_of_epi _
  asIso e

@[reassoc (attr := simp)]
lemma isoKernel_of_exact_comp_ι {K A B : C} {f : A ⟶ B} {i : K ⟶ A} 
    (h1 : Exact i f) (h2 : Exact (0 : 0 ⟶ K) i) :
    (isoKernel_of_exact h1 h2).hom ≫ kernel.ι _ = i := by
  let e : K ⟶ kernel f := kernel.lift f i h1.w
  haveI : Epi e := Exact.epi_kernel_lift h1
  haveI : Mono i := by rwa [mono_iff_exact_zero_left]
  haveI : Mono e := by
    constructor
    intro Z a b h
    rw [← cancel_mono (kernel.ι f)] at h
    simp only [Category.assoc, kernel.lift_ι, zero_comp] at h
    rwa [cancel_mono i] at h
  haveI : IsIso e := isIso_of_mono_of_epi _
  simp [isoKernel_of_exact]

lemma map_isZero {X : C} (G : C ⥤ D) [G.Additive] (hX : IsZero X) :
  IsZero (G.obj X) := sorry

noncomputable
def preservesKernelsOfExact (G : C ⥤ D) [G.Additive]
    (hG : ∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Exact f g), Exact (G.map f) (G.map g)) 
    (A B : C) (e : A ⟶ B) :
  PreservesLimit (parallelPair e 0) G :=
    preservesLimitOfPreservesLimitCone (limit.isLimit _) <| {
      lift := fun E => 
        let ee : E.pt ⟶ kernel (G.map e) := kernel.lift _ (E.π.app .zero) sorry
        haveI h1 : Exact (G.map (kernel.ι e)) (G.map e) := by
          apply hG
          exact exact_kernel_ι
        haveI h2 : Exact 0 (G.map (kernel.ι e)) := by
          let z : G.obj 0 ≅ 0 := IsZero.iso (map_isZero _ <| isZero_zero _) (isZero_zero _)
          have : z.hom ≫ (0 : 0 ⟶ G.obj (kernel e)) = 0 := by simp 
          rw [← exact_iso_comp (f := z.hom)]
          have : z.hom ≫ (0 : 0 ⟶ G.obj (kernel e)) = G.map 0 := by simp
          rw [this]
          apply hG
          rw [← mono_iff_exact_zero_left]
          infer_instance
        ee ≫ Iso.inv (isoKernel_of_exact h1 h2)
      fac := sorry
      uniq := sorry
    }  

noncomputable 
def preservesFiniteLimitsOfExact (G : C ⥤ D) [G.Additive]
  (hG : ∀ ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Exact f g), Exact (G.map f) (G.map g)) :
  PreservesFiniteLimits G := 
  haveI : ∀ {X Y : C} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) G := 
    preservesKernelsOfExact _ hG _ _
  Functor.preservesFiniteLimitsOfPreservesKernels G

def preservesFiniteCoLimitsOfExact (G : C ⥤ D)
  (hG : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Exact f g), Exact (G.map f) (G.map g)) :
  PreservesFiniteColimits G := sorry

def exactOfPreserves {X Y Z : C} (G : C ⥤ D) [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : Exact f g) : Exact (G.map f) (G.map g) := sorry
