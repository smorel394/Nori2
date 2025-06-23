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

noncomputable def contractLeftToRight {X Y : ComposableArrows A 2} (u : X ⟶ Y) :
    (contractLeft A).obj X ⟶ (contractRight A).obj Y := by
  refine CochainComplex.ofHom _ _ (contractLeft_obj_sq X) _ _ (contractRight_obj_sq Y)
    (fun i ↦ ?_) (fun i ↦ ?_)
  · match i with
    | 0 => exact kernel.ι _ ≫ u.app 0
    | 1 => exact u.app 1
    | 2 => exact u.app 2 ≫ cokernel.π _
  · match i with
    | 0 => dsimp [contractRight_obj_d, contractLeft_obj_d]; simp
    | 1 => dsimp [contractRight_obj_d, contractLeft_obj_d]; simp
    | 2 => dsimp [contractRight_obj_d, contractLeft_obj_d]; simp

variable (A)

noncomputable def contractNatTrans : contractLeft A ⟶ contractRight A where
  app X := contractLeftToRight (𝟙 X)
  naturality X Y f := by
    ext i
    match i with
    | 0 => dsimp [contractLeftToRight]; simp
    | 1 => dsimp [contractLeftToRight]; erw [comp_id, id_comp]
    | 2 => dsimp [contractLeftToRight]; erw [id_comp, id_comp]; simp

instance contractNatTrans_mono (X : ComposableArrows A 2) :
    Mono (HomologicalComplex.homologyMap ((contractNatTrans A).app X) 1) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A₀ a₀ h₀
  obtain ⟨A₁, π, _, a₁, h₁⟩ := (epi_iff_surjective_up_to_refinements
    (((contractLeft A).obj X).homologyπ 1)).mp inferInstance a₀
  have eq : ((contractLeft A).obj X).iCycles 1 ≫ ((contractRight A).obj X).pOpcycles 1 =
      ((contractLeft A).obj X).homologyπ 1 ≫ HomologicalComplex.homologyMap
      ((contractNatTrans A).app X) 1 ≫ ((contractRight A).obj X).homologyι 1 := by
    have : ((contractRight A).obj X).pOpcycles 1 = ((contractLeft A).obj X).pOpcycles 1 ≫
        HomologicalComplex.opcyclesMap ((contractNatTrans A).app X) 1 := by
      rw [HomologicalComplex.p_opcyclesMap]
      change _ = 𝟙 _ ≫ _
      rw [id_comp]
    rw [this, ← assoc, ← HomologicalComplex.homology_π_ι, assoc,
      HomologicalComplex.homologyι_naturality]
  have : (a₁ ≫ ((contractLeft A).obj X).iCycles 1) ≫
      ((contractRight A).obj X).pOpcycles 1 = 0 := by
    rw [assoc, eq, ← assoc, ← h₁, assoc, ← assoc a₀, h₀, zero_comp, comp_zero]
  have : (a₁ ≫ ((contractLeft A).obj X).iCycles 1) ≫ cokernel.π (X.map' 0 1) = 0 := by
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
  set a₂ : A₁ ⟶ Abelian.image (X.map' 0 1) :=
    kernel.lift (cokernel.π (X.map' 0 1)) (a₁ ≫ ((contractLeft A).obj X).iCycles 1) this
  have h₂ : a₂ ≫ Abelian.image.ι (X.map' 0 1) = a₁ ≫ ((contractLeft A).obj X).iCycles 1 := by
    simp [a₂]
  obtain ⟨A₃, π', _, a₃, h₃⟩ := (epi_iff_surjective_up_to_refinements
    (Abelian.factorThruImage (X.map' 0 1))).mp inferInstance a₂
  have zero : a₃ ≫ X.map' 0 1 ≫ X.map' 1 2 = 0 := by
    rw [← Abelian.image.fac (X.map' 0 1), ← assoc, ← assoc, ← h₃]
    slice_lhs 2 3 => rw [h₂]
    have : X.map' 1 2 = ((contractLeft A).obj X).d 1 2 := by
      dsimp [contractLeft]
      erw [CochainComplex.of_d]
      rfl
    rw [this]
    simp
  set a₄ : A₃ ⟶ ((contractLeft A).obj X).X 0 := kernel.lift (X.map' 0 1 ≫ X.map' 1 2) a₃ zero
  have h₄ : a₄ ≫ ((contractLeft A).obj X).toCycles 0 1 ≫ ((contractLeft A).obj X).homologyπ 1 =
      π' ≫ π ≫ a₀ := by
    rw [h₁, ← assoc, ← assoc]
    congr 1
    rw [← cancel_mono (((contractLeft A).obj X).iCycles 1), assoc π', ← h₂, ← assoc π', h₃,
      assoc a₃, Abelian.image.fac, assoc a₄, HomologicalComplex.toCycles_i]
    erw [CochainComplex.of_d _ _ (contractLeft_obj_sq X)]
    change a₄ ≫ kernel.ι _ ≫ X.map' 0 1 = _
    rw [kernel.lift_ι_assoc]
  rw [← cancel_epi π, ← cancel_epi π', ← h₄]
  simp

instance contractNatTrans_epi (X : ComposableArrows A 2) :
    Epi (HomologicalComplex.homologyMap ((contractNatTrans A).app X) 1) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A₀ a₀
  obtain ⟨A₁, π, _, a₁, h₁⟩ := (epi_iff_surjective_up_to_refinements
    (((contractRight A).obj X).homologyπ 1)).mp inferInstance a₀
  have zero : (a₁ ≫ ((contractRight A).obj X).iCycles 1 ≫ ((contractLeft A).obj X).d 1 2) ≫
      ((contractNatTrans A).app X).f 2 = 0 := by
    rw [assoc, assoc, ← ((contractNatTrans A).app X).comm]
    change _ ≫ _ ≫ 𝟙 _ ≫ _ = 0
    simp
  set a₂ : A₁ ⟶ Abelian.image (X.map' 0 1 ≫ X.map' 1 2) :=
    kernel.lift (cokernel.π _) (a₁ ≫ ((contractRight A).obj X).iCycles 1 ≫
    ((contractLeft A).obj X).d 1 2)
    (by dsimp [contractNatTrans, contractLeftToRight] at zero; erw [id_comp] at zero; exact zero)
  have h₂ : a₂ ≫ Abelian.image.ι _ = a₁ ≫ ((contractRight A).obj X).iCycles 1 ≫
      ((contractLeft A).obj X).d 1 2 := by simp [a₂]
  obtain ⟨A₃, π', _, a₃, h₃⟩ := (epi_iff_surjective_up_to_refinements
    (Abelian.factorThruImage (X.map' 0 1 ≫ X.map' 1 2))).mp inferInstance a₂
  set a₁' := π' ≫ a₁ ≫ ((contractRight A).obj X).iCycles 1 - a₃ ≫ ((contractRight A).obj X).d 0 1
  have zero' : a₁' ≫ ((contractLeft A).obj X).d 1 2 = 0 := by
    simp only [Preadditive.sub_comp, assoc, a₁']
    erw [CochainComplex.of_d, CochainComplex.of_d]
    change _ - a₃ ≫ X.map' 0 1 ≫ X.map' 1 2 = 0
    rw [← Abelian.image.fac (X.map' 0 1 ≫ X.map' 1 2), ← assoc a₃, ← h₃, assoc π', h₂]
    dsimp [contractRight]
    erw [CochainComplex.of_d]
    simp
  set a₂' : A₃ ⟶ ((contractLeft A).obj X).cycles 1 :=
    ((contractLeft A).obj X).liftCycles a₁' 2 (by simp) zero'
  have h₂' : a₂' ≫ ((contractLeft A).obj X).iCycles 1 = a₁' := by simp [a₂']
  have eq : (a₂' ≫ ((contractLeft A).obj X).homologyπ 1) ≫
      HomologicalComplex.homologyMap ((contractNatTrans A).app X) 1 = (π' ≫ π) ≫ a₀ := by
    rw [assoc, HomologicalComplex.homologyπ_naturality]
    have : a₂' ≫ HomologicalComplex.cyclesMap ((contractNatTrans A).app X) 1 =
        π' ≫ a₁ - a₃ ≫ ((contractRight A).obj X).toCycles 0 1 := by
      rw [← cancel_mono (((contractRight A).obj X).iCycles 1)]
      simp only [assoc, HomologicalComplex.cyclesMap_i, Preadditive.sub_comp,
        HomologicalComplex.toCycles_i]
      rw [← assoc a₂', h₂']
      simp only [Preadditive.sub_comp, assoc, a₁']
      change _ ≫ _ ≫ _ ≫ 𝟙 _ - _ ≫ _ ≫ 𝟙 _ = _
      rw [comp_id, comp_id]
    rw [← assoc a₂', this, Preadditive.sub_comp, assoc π' a₁, ← h₁]
    simp
  exact ⟨A₃, π' ≫ π, inferInstance, a₂' ≫ ((contractLeft A).obj X).homologyπ 1, eq.symm⟩

instance contractNatTrans_iso (X : ComposableArrows A 2) :
    IsIso (HomologicalComplex.homologyMap ((contractNatTrans A).app X) 1) :=
  isIso_of_mono_of_epi _

lemma comp_contractNatTrans {X Y : ComposableArrows A 2} (u : X ⟶ Y) :
    (contractLeft A).map u ≫ (contractNatTrans A).app Y = contractLeftToRight u := by
  ext i
  match i with
  | 0 => dsimp [contractNatTrans, contractLeftToRight]; simp
  | 1 => dsimp [contractNatTrans, contractLeftToRight]; erw [comp_id]
  | 2 => dsimp [contractNatTrans, contractLeftToRight]; erw [id_comp]

lemma contractNatTrans_comp {X Y : ComposableArrows A 2} (u : X ⟶ Y) :
    (contractNatTrans A).app X ≫ (contractRight A).map u = contractLeftToRight u := by
  ext i
  match i with
  | 0 => dsimp [contractNatTrans, contractLeftToRight]; simp
  | 1 => dsimp [contractNatTrans, contractLeftToRight]; erw [id_comp]
  | 2 => dsimp [contractNatTrans, contractLeftToRight]; erw [id_comp]; simp

end Contract

lemma homologyLeft_map_eq_of_homotopic {X Y : ComposableArrows A 2} (u v : X ⟶ Y)
    (h : homotopic u v) : (homologyLeft A).map u = (homologyLeft A).map v := by
  rw [← cancel_mono (HomologicalComplex.homologyMap ((contractNatTrans A).app Y) 1)]
  simp only [Functor.comp_map, homologyLeft, HomologicalComplex.homologyFunctor_map]
  rw [← HomologicalComplex.homologyMap_comp, comp_contractNatTrans,
    ← HomologicalComplex.homologyMap_comp, comp_contractNatTrans]
  obtain ⟨σ₁, σ₂, eq⟩ := h
  refine ShortComplex.Homotopy.homologyMap_congr ?_
  simp [HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
  simp [contractLeftToRight]
  refine {h₀ := ?_, h₀_f := ?_, h₁ := ?_, h₂ := ?_, h₃ := 0,
           g_h₃ := by simp, comm₁ := ?_, comm₂ := ?_, comm₃ := ?_}
  · erw [HomologicalComplex.shortComplexFunctor_obj_X₁]
    simp
    exact kernel.ι _ ≫ (u.app zero + X.map' 0 1 ≫ σ₁ - v.app zero)
  · simp
    change (kernel.ι _ ≫ (u.app zero + X.map' 0 1 ≫ σ₁ - v.app zero)) ≫ _ = 0
  · erw [HomologicalComplex.shortComplexFunctor_obj_X₂]
    erw [HomologicalComplex.shortComplexFunctor_obj_X₁]
    simp only [CochainComplex.of_x, CochainComplex.prev, sub_self]
    exact σ₁
  · erw [HomologicalComplex.shortComplexFunctor_obj_X₂]
    erw [HomologicalComplex.shortComplexFunctor_obj_X₃]
    simp only [CochainComplex.next, CochainComplex.of_x]
    exact σ₂
  · dsimp
    simp
  · sorry
  · sorry


section Lift

variable (A)

def lift : Adel C ⥤ A := sorry

end Lift

end Adel

end CategoryTheory
