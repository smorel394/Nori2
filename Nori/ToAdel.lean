import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Nori.Adel

universe u v u' v'

open CategoryTheory Category Functor Limits

open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CategoryTheory

namespace Adel

noncomputable def functor_aux : C ⥤ ComposableArrows C 2 where
  obj X := ComposableArrows.mk₂ (0 : 0 ⟶ X) (0 : X ⟶ 0)
  map f := ComposableArrows.homMk₂ 0 f 0 (by simp) (by change _ = f ≫ 0; simp)
  map_id X := by
    refine ComposableArrows.hom_ext₂ (by simp) (by simp) ?_
    change 0 = 𝟙 0
    simp
  map_comp f g := by
    refine ComposableArrows.hom_ext₂ (by simp) (by simp) ?_
    change 0 = 0 ≫ 0
    simp

noncomputable def functor : C ⥤ Adel C := functor_aux C ⋙ quotient C

variable {C} {A : Type u'} [Category.{v'} A] [Abelian A] (F : C ⥤ A) [F.Additive]

section ContractLeft

noncomputable def contractLeft_obj_X (X : ComposableArrows A 2) (i : Fin 3) : A := match i with
  | 0 => kernel (X.map' 0 1 ≫ X.map' 1 2)
  | 1 => X.obj 1
  | 2 => X.obj 2

noncomputable def contractLeft_obj_d (X : ComposableArrows A 2) (i : Fin 3) :
  contractLeft_obj_X X i ⟶ contractLeft_obj_X X (i + 1) := match i with
  | 0 => kernel.ι _ ≫ X.map' 0 1
  | 1 => X.map' 1 2
  | 2 => 0

noncomputable def contractLeft_obj_sq (X : ComposableArrows A 2) (i : Fin 3) :
  contractLeft_obj_d X i ≫ contractLeft_obj_d X (i + 1) = 0 := match i with
  | 0 => by dsimp [contractLeft_obj_d]; simp
  | 1 => by dsimp [contractLeft_obj_d]; simp
  | 2 => by dsimp [contractLeft_obj_d]; simp

variable (A)

noncomputable abbrev contractLeft : ComposableArrows A 2 ⥤ CochainComplex A (Fin 3) where
  obj X := CochainComplex.of (contractLeft_obj_X X) (contractLeft_obj_d X) (contractLeft_obj_sq X)
  map {X Y} f := by
    refine CochainComplex.ofHom (contractLeft_obj_X X) (contractLeft_obj_d X)
      (contractLeft_obj_sq X) (contractLeft_obj_X Y) (contractLeft_obj_d Y) (contractLeft_obj_sq Y)
      (fun i ↦ ?_) (fun i ↦ ?_)
    · match i with
      | 0 => refine kernel.lift (Y.map' 0 1 ≫ Y.map' 1 2) (kernel.ι _ ≫ f.app 0) ?_
             dsimp
             simp only [Fin.isValue, homOfLE_leOfHom, assoc]
             rw [← NatTrans.naturality_assoc, ← NatTrans.naturality, ← assoc _ _ (f.app 2),
               kernel.condition_assoc, zero_comp]
      | 1 => exact f.app 1
      | 2 => exact f.app 2
    · match i with
      | 0 => dsimp [contractLeft_obj_d]; simp
      | 1 => dsimp [contractLeft_obj_d]; simp
      | 2 => dsimp [contractLeft_obj_d]; simp
  map_id X := by
    refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
    match i with
    | 0 => dsimp [contractLeft_obj_X]; simp
    | 1 => dsimp [contractLeft_obj_X]
    | 2 => dsimp [contractLeft_obj_X]
  map_comp f g := by
    refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
    match i with
    | 0 => dsimp [contractLeft_obj_X]
           rw [← (cancel_mono (kernel.ι _))]
           simp
    | 1 => dsimp [contractLeft_obj_X]
    | 2 => dsimp [contractLeft_obj_X]

noncomputable def homologyLeft : ComposableArrows A 2 ⥤ A :=
  contractLeft A ⋙ HomologicalComplex.homologyFunctor _ _ 1

end ContractLeft

section ContractRight

noncomputable def contractRight_obj_X (X : ComposableArrows A 2) (i : Fin 3) : A := match i with
  | 0 => X.obj 0
  | 1 => X.obj 1
  | 2 => cokernel (X.map' 0 1 ≫ X.map' 1 2)

noncomputable def contractRight_obj_d (X : ComposableArrows A 2) (i : Fin 3) :
  contractRight_obj_X X i ⟶ contractRight_obj_X X (i + 1) := match i with
  | 0 => X.map' 0 1
  | 1 => X.map' 1 2 ≫ cokernel.π _
  | 2 => 0

noncomputable def contractRight_obj_sq (X : ComposableArrows A 2) (i : Fin 3) :
  contractRight_obj_d X i ≫ contractRight_obj_d X (i + 1) = 0 := match i with
  | 0 => by dsimp [contractRight_obj_d]; rw [← assoc, cokernel.condition]
  | 1 => by dsimp [contractRight_obj_d]; simp
  | 2 => by dsimp [contractRight_obj_d]; simp

variable (A)

noncomputable abbrev contractRight : ComposableArrows A 2 ⥤ CochainComplex A (Fin 3) where
  obj X := CochainComplex.of (contractRight_obj_X X) (contractRight_obj_d X) (contractRight_obj_sq X)
  map {X Y} f := by
    refine CochainComplex.ofHom (contractRight_obj_X X) (contractRight_obj_d X)
      (contractRight_obj_sq X) (contractRight_obj_X Y) (contractRight_obj_d Y) (contractRight_obj_sq Y)
      (fun i ↦ ?_) (fun i ↦ ?_)
    · match i with
      | 0 => exact f.app 0
      | 1 => exact f.app 1
      | 2 => refine cokernel.desc (X.map' 0 1 ≫ X.map' 1 2) (f.app 2 ≫ cokernel.π _) ?_
             dsimp
             simp only [Fin.isValue, homOfLE_leOfHom, assoc, NatTrans.naturality_assoc]
             rw [← assoc (Y.map _) (Y.map _), cokernel.condition, comp_zero]
    · match i with
      | 0 => dsimp [contractRight_obj_d]; simp
      | 1 => dsimp [contractRight_obj_d]; simp
      | 2 => dsimp [contractRight_obj_d]; simp
  map_id X := by
    refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
    match i with
    | 0 => dsimp [contractRight_obj_X]
    | 1 => dsimp [contractRight_obj_X]
    | 2 => dsimp [contractRight_obj_X]; simp
  map_comp f g := by
    refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
    match i with
    | 0 => dsimp [contractRight_obj_X]
    | 1 => dsimp [contractRight_obj_X]
    | 2 => dsimp [contractRight_obj_X]
           rw [← cancel_epi (cokernel.π _)]
           simp

noncomputable def homologyRight : ComposableArrows A 2 ⥤ A :=
  contractRight A ⋙ HomologicalComplex.homologyFunctor _ _ 1

end ContractRight

section Contract

variable (A)

noncomputable def contractNatTrans : contractLeft A ⟶ contractRight A where
  app X := by
    refine CochainComplex.ofHom _ _ (contractLeft_obj_sq X) _ _ (contractRight_obj_sq X)
      (fun i ↦ ?_) (fun i ↦ ?_)
    · match i with
      | 0 => exact kernel.ι _
      | 1 => exact 𝟙 _
      | 2 => exact cokernel.π _
    · match i with
      | 0 => dsimp [contractRight_obj_d, contractLeft_obj_d]; simp
      | 1 => dsimp [contractRight_obj_d, contractLeft_obj_d]; simp
      | 2 => dsimp [contractRight_obj_d, contractLeft_obj_d]; simp
  naturality X Y f := by
    ext i
    match i with
    | 0 => dsimp; simp
    | 1 => dsimp; simp
    | 2 => dsimp; simp

lemma contractNatTrans_mono (X : ComposableArrows A 2) :
    Mono (HomologicalComplex.homologyMap ((contractNatTrans A).app X) 1) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T a ha
  obtain ⟨A', π, _, a', ha'⟩ := (epi_iff_surjective_up_to_refinements
    (((contractLeft A).obj X).homologyπ 1)).mp inferInstance a
  have eq : ((contractLeft A).obj X).iCycles 1 ≫ ((contractRight A).obj X).pOpcycles 1 =
    ((contractLeft A).obj X).homologyπ 1 ≫ HomologicalComplex.homologyMap
    ((contractNatTrans A).app X) 1 ≫ ((contractRight A).obj X).homologyι 1 := sorry
  have : (a' ≫ ((contractLeft A).obj X).iCycles 1) ≫
      ((contractRight A).obj X).pOpcycles 1 = 0 := by
    rw [assoc, eq, ← assoc, ← ha', assoc, ← assoc a, ha, zero_comp, comp_zero]
  have : (a' ≫ ((contractLeft A).obj X).iCycles 1) ≫ cokernel.π (X.map' 0 1) = 0 := by
    have eq : (((contractRight A).obj X).d 0 1) = X.map' 0 1 := by
      dsimp [contractRight]
      erw [CochainComplex.of_d]
      rfl
    set e := ((((contractRight A).obj X).opcyclesIsCokernel 0 1 (by simp)).coconePointUniqueUpToIso
        (cokernelIsCokernel _)).trans (cokernelIsoOfEq eq)
    rw [← cancel_mono e.inv]
    dsimp [e]
    rw [assoc, π_comp_cokernelIsoOfEq_inv_assoc]
    erw [(((contractRight A).obj X).opcyclesIsCokernel 0 1
      (by simp)).comp_coconePointUniqueUpToIso_inv (cokernelIsCokernel _) WalkingParallelPair.one]
    simp [this]
  set a'' : A' ⟶ Abelian.image (X.map' 0 1) :=
    kernel.lift (cokernel.π (X.map' 0 1)) (a' ≫ ((contractLeft A).obj X).iCycles 1) this
  have ha'' : a'' ≫ Abelian.image.ι (X.map' 0 1) = a' ≫ ((contractLeft A).obj X).iCycles 1 := by
    simp [a'']
  obtain ⟨A'', π', _, a''', ha'''⟩ := (epi_iff_surjective_up_to_refinements
    (Abelian.factorThruImage (X.map' 0 1))).mp inferInstance a''
  have zero : a''' ≫ X.map' 0 1 ≫ X.map' 1 2 = 0 := by
    rw [← Abelian.image.fac (X.map' 0 1), ← assoc, ← assoc, ← ha''']
    slice_lhs 2 3 => rw [ha'']
    have : X.map' 1 2 = ((contractLeft A).obj X).d 1 2 := by
      dsimp [contractLeft]
      erw [CochainComplex.of_d]
      rfl
    rw [this]
    simp





end Contract


#exit
noncomputable def homotopy_of_homotopic {X Y : ComposableArrows A 2} (u v : X ⟶ Y)
    (h : homotopic u v) : Homotopy ((contractLeft A).map u) ((contractLeft A).map v) where
  hom i j := match i, j with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 1, 0 => sorry
  | 1, 1 => 0
  | 1, 2 => 0
  | 2, 0 => 0
  | 2, 1 => sorry
  | 2, 2 => 0
  zero := sorry
  comm := sorry

lemma homology_map_eq_of_homotopic {X Y : ComposableArrows A 2} (u v : X ⟶ Y)
    (h : homotopic u v) : (homology A).map u = (homology A).map v :=
  Homotopy.homologyMap_eq (homotopy_of_homotopic u v h) _

section Lift

variable (A)

def lift : Adel C ⥤ A := sorry

end Lift

end Adel

end CategoryTheory
