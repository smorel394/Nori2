import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ExactSequence
import Nori.Mathlib.CategoryTheory.Quotient.Preadditive
import Nori.Mathlib.Algebra.Homology.ShortComplex.Basic
import Nori.Adel

universe u v u' v'

open CategoryTheory Category Functor Limits

open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CategoryTheory

namespace Adel

-- A variant of `functor_aux` that lands in `ShortComplex C`.
noncomputable def functor_aux_complex : C ⥤ ShortComplex C where
  obj X := ShortComplex.mk (0 : 0 ⟶ X) (0 : X ⟶ 0) (by simp)
  map f := ShortComplex.homMk 0 f 0 (by simp) (by simp)
  map_id X := ShortComplex.hom_ext _ _ (by simp) (by simp) (by simp)
  map_comp f g := ShortComplex.hom_ext _ _ (by simp) (by simp) (by simp)

noncomputable def functor_aux : C ⥤ ComposableArrows C 2 where
  obj X := ((functor_aux_complex C).obj X).toComposableArrows
  map f := ShortComplex.mapToComposableArrows ((functor_aux_complex C).map f)

noncomputable def functor : C ⥤ Adel C := functor_aux C ⋙ quotient C

instance : (functor_aux_complex C).Additive where
  map_add {_ _ _ _} := by
    ext
    · dsimp [functor_aux_complex]; simp
    · dsimp [functor_aux_complex]
    · dsimp [functor_aux_complex]; simp

instance : (functor_aux C).Additive where
  map_add {_ _ _ _} := by
    dsimp [functor_aux]; simp
    ext
    · dsimp
    · dsimp
    · dsimp

instance : (functor C).Additive where
  map_add {_ _ _ _} := by
    dsimp [functor]; simp

variable {C} {A : Type u'} [Category.{v'} A] [Abelian A]

variable (A) in
noncomputable def functor_aux_homology :
    functor_aux_complex A ⋙ ShortComplex.homologyFunctor A ≅ 𝟭 A := by
  refine NatIso.ofComponents (fun X ↦ (((functor_aux_complex A).obj X).asIsoHomologyπ rfl).symm
                                      ≪≫ ((functor_aux_complex A).obj X).cyclesIsoX₂ rfl) ?_
  intro X Y f
  dsimp
  rw [← cancel_epi (((functor_aux_complex A).obj X).asIsoHomologyπ rfl).hom]
  conv_rhs => change _ ≫ _ ≫ ((functor_aux_complex A).map f).τ₂
              rw [assoc, ← ShortComplex.cyclesMap_i, Iso.hom_inv_id_assoc]
  rw [ShortComplex.asIsoHomologyπ_hom, ShortComplex.homologyπ_naturality_assoc]
  simp

section ContractLeft

variable (A)

/-! This is the right of the fully faithful inclusion `ShortComplex A ⥤ ComposableArrows A 2`-/
noncomputable def contractLeft : ComposableArrows A 2 ⥤ ShortComplex A where
  obj X := ShortComplex.mk (kernel.ι (X.map' 0 1 ≫ X.map' 1 2) ≫ X.map' 0 1) (X.map' 1 2) (by simp)
  map {X Y} u := by
    refine ShortComplex.homMk ?_ (u.app 1) (u.app 2) ?_ ?_
    · refine kernel.lift _ (kernel.ι _ ≫ u.app 0) ?_
      simp only [assoc]
      rw [← NatTrans.naturality_assoc, ← NatTrans.naturality, ← assoc _ _ (u.app two),
        ← assoc (kernel.ι _)]
      simp
    · dsimp; simp
    · dsimp; simp
  map_id X := by
    ext
    · dsimp; simp
    · rfl
    · rfl
  map_comp f g := by
    ext
    · dsimp; simp
    · rfl
    · rfl

instance : (contractLeft A).Additive where
  map_add {_ _ _ _} := by
    ext
    · rw [← cancel_mono (kernel.ι _)]
      dsimp [contractLeft]; simp
    · dsimp [contractLeft]
    · dsimp [contractLeft]

noncomputable def functor_contractLeft :
    functor_aux A ⋙ contractLeft A ≅ functor_aux_complex A := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine ShortComplex.isoMk ?_ (Iso.refl _) (Iso.refl _) ?_ ?_
    · have : IsIso (kernel.ι (((functor_aux A).obj X).map' 0 1 ≫
          ((functor_aux A).obj X).map' 1 2)) :=
        KernelFork.IsLimit.isIso_ι _ (limit.isLimit (parallelPair _ 0))
        (by change 0 ≫ 0 = 0; simp)
      exact asIso (kernel.ι _)
    · dsimp [functor_aux_complex, functor_aux, contractLeft]
      simp
    · dsimp; simp; rfl
  · intro X Y f
    dsimp
    ext
    · dsimp [contractLeft, functor_aux]
      simp
    · dsimp; simp; rfl
    · dsimp; simp; rfl

noncomputable def homologyLeft : ComposableArrows A 2 ⥤ A :=
  contractLeft A ⋙ ShortComplex.homologyFunctor _

instance : (homologyLeft A).Additive := by
  dsimp [homologyLeft]
  infer_instance

variable {A} {B : Type u} [Category.{v} B] [Abelian B] (G : A ⥤ B) [PreservesFiniteLimits G]

noncomputable def contractLeft_functoriality :
    G.mapComposableArrows 2 ⋙ contractLeft B ≅ contractLeft A ⋙ G.mapShortComplex := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun u ↦ ?_)
  · refine ShortComplex.isoMk ?_ (Iso.refl _) (Iso.refl _) ?_ ?_
    · exact kernelIsoOfEq (f := G.map (X.map' 0 1) ≫ G.map (X.map' 1 2))
        (g := G.map (X.map' 0 1 ≫ X.map' 1 2)) (by simp) ≪≫
        (PreservesKernel.iso G (X.map' 0 1 ≫ X.map' 1 2)).symm
    · dsimp [contractLeft]; simp
    · dsimp [contractLeft]; simp
  · ext
    · rw [← cancel_mono (PreservesKernel.iso G _).hom, ← cancel_mono (kernel.ι _)]
      dsimp [contractLeft]; simp
    · dsimp [contractLeft]; simp
    · dsimp [contractLeft]; simp

variable {G} {G' : A ⥤ B} [PreservesFiniteLimits G'] (α : G ⟶ G')

attribute [local instance] Functor.additive_of_preserves_binary_products

lemma contractLeft_functoriality_naturality : whiskerRight
    ((whiskeringRight (Fin 3) A B).map α) (contractLeft B) ≫
    (contractLeft_functoriality G').hom = (contractLeft_functoriality G).hom ≫
    whiskerLeft (contractLeft A) (NatTrans.mapShortComplex α) := by
  dsimp [contractLeft, contractLeft_functoriality, NatTrans.mapShortComplex]
  ext
  · dsimp
    rw [← cancel_mono (PreservesKernel.iso G' _).hom, assoc, assoc, Iso.inv_hom_id]
    rw [← cancel_mono (kernel.ι _)]
    simp only [comp_id, lift_comp_kernelIsoOfEq_hom, kernel.lift_ι, assoc,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
    rw [← α.naturality, ← assoc, ← assoc]
    congr 1
    simp
  · dsimp; simp
  · dsimp; simp

end ContractLeft

section ContractRight

variable (A)

noncomputable def contractRight : ComposableArrows A 2 ⥤ ShortComplex A where
  obj X := ShortComplex.mk (X.map' 0 1) (X.map' 1 2 ≫ cokernel.π (X.map' 0 1 ≫ X.map' 1 2))
    (by rw [← assoc, cokernel.condition])
  map {X Y} u := by
    refine ShortComplex.homMk (u.app 0) (u.app 1) ?_ ?_ ?_
    · refine cokernel.desc _ (u.app 2 ≫ cokernel.π _) ?_
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
        ComposableArrows.map', homOfLE_leOfHom, assoc, NatTrans.naturality_assoc]
      conv_lhs => congr; rfl; rw [← assoc (Y.map _), cokernel.condition]
      rw [comp_zero]
    · dsimp; simp
    · dsimp; simp
  map_id X := by
    ext
    · rfl
    · rfl
    · dsimp; simp
  map_comp f g := by
    ext
    · rfl
    · rfl
    · dsimp; simp

instance : (contractRight A).Additive where
  map_add {_ _ _ _ } := by
    ext
    · dsimp [contractRight]
    · dsimp [contractRight]
    · rw [← cancel_epi (cokernel.π _)]
      dsimp [contractRight]; simp

noncomputable def functor_contractRight :
    functor_aux_complex A ≅ functor_aux A ⋙ contractRight A := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · have : IsIso (cokernel.π (((functor_aux A).obj X).map' 0 1 ≫
          ((functor_aux A).obj X).map' 1 2)) :=
        CokernelCofork.IsColimit.isIso_π _ (colimit.isColimit (parallelPair _ 0))
        (by change 0 ≫ 0 = 0; simp)
      exact asIso (cokernel.π _)
    · dsimp; simp; rfl
    · dsimp; simp; rfl
  · intro X Y f
    dsimp
    ext
    · dsimp; simp; rfl
    · dsimp; simp; rfl
    · dsimp [contractRight, functor_aux]
      simp

noncomputable def homologyRight : ComposableArrows A 2 ⥤ A :=
  contractRight A ⋙ ShortComplex.homologyFunctor _

instance : (homologyRight A).Additive := by
  dsimp [homologyRight]
  infer_instance

end ContractRight

section Contract

noncomputable def contractLeftToRight {X Y : ComposableArrows A 2} (u : X ⟶ Y) :
    (contractLeft A).obj X ⟶ (contractRight A).obj Y := by
  refine ShortComplex.homMk (kernel.ι _ ≫ u.app 0) (u.app 1) (u.app 2 ≫ cokernel.π _) ?_ ?_
  · dsimp [contractLeft, contractRight]; simp
  · dsimp [contractLeft, contractRight]; simp

variable (A)

noncomputable def contractNatTrans : contractLeft A ⟶ contractRight A where
  app X := contractLeftToRight (𝟙 X)
  naturality X Y f := by
    dsimp [contractLeftToRight, contractLeft, contractRight]
    ext
    · simp
    · simp
    · simp

instance contractNatTrans_mono (X : ComposableArrows A 2) :
    Mono (ShortComplex.homologyMap ((contractNatTrans A).app X)) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A₀ a₀ h₀
  obtain ⟨A₁, π, _, a₁, h₁⟩ := (epi_iff_surjective_up_to_refinements
    ((contractLeft A).obj X).homologyπ).mp inferInstance a₀
  have eq : ((contractLeft A).obj X).iCycles ≫ ((contractRight A).obj X).pOpcycles =
      ((contractLeft A).obj X).homologyπ ≫ ShortComplex.homologyMap
      ((contractNatTrans A).app X) ≫ ((contractRight A).obj X).homologyι := by
    have : ((contractRight A).obj X).pOpcycles = ((contractLeft A).obj X).pOpcycles ≫
        ShortComplex.opcyclesMap ((contractNatTrans A).app X) := by
      rw [ShortComplex.p_opcyclesMap]
      change _ = 𝟙 _ ≫ _
      rw [id_comp]
    rw [this, ← assoc, ← ShortComplex.homology_π_ι, assoc, ShortComplex.homologyι_naturality]
  have : (a₁ ≫ ((contractLeft A).obj X).iCycles) ≫ ((contractRight A).obj X).pOpcycles = 0 := by
    rw [assoc, eq, ← assoc, ← h₁, assoc, ← assoc a₀, h₀, zero_comp, comp_zero]
  have : (a₁ ≫ ((contractLeft A).obj X).iCycles) ≫ cokernel.π (X.map' 0 1) = 0 := by
    set e := ((contractRight A).obj X).opcyclesIsCokernel.coconePointUniqueUpToIso
        (cokernelIsCokernel _)
    rw [← cancel_mono e.inv]
    dsimp [e]
    rw [assoc]
    erw [((contractRight A).obj X).opcyclesIsCokernel.comp_coconePointUniqueUpToIso_inv
      (cokernelIsCokernel _) WalkingParallelPair.one]
    simp [this]
  set a₂ : A₁ ⟶ Abelian.image (X.map' 0 1) :=
    kernel.lift (cokernel.π (X.map' 0 1)) (a₁ ≫ ((contractLeft A).obj X).iCycles) this
  have h₂ : a₂ ≫ Abelian.image.ι (X.map' 0 1) = a₁ ≫ ((contractLeft A).obj X).iCycles:= by
    simp [a₂]
  obtain ⟨A₃, π', _, a₃, h₃⟩ := (epi_iff_surjective_up_to_refinements
    (Abelian.factorThruImage (X.map' 0 1))).mp inferInstance a₂
  have zero : a₃ ≫ X.map' 0 1 ≫ X.map' 1 2 = 0 := by
    rw [← Abelian.image.fac (X.map' 0 1), ← assoc, ← assoc, ← h₃]
    slice_lhs 2 3 => rw [h₂]
    change _ ≫ _ ≫ ((contractLeft A).obj X).g = 0
    simp
  set a₄ : A₃ ⟶ ((contractLeft A).obj X).X₁ := kernel.lift (X.map' 0 1 ≫ X.map' 1 2) a₃ zero
  have h₄ : a₄ ≫ ((contractLeft A).obj X).toCycles ≫ ((contractLeft A).obj X).homologyπ =
      π' ≫ π ≫ a₀ := by
    rw [h₁, ← assoc, ← assoc]
    congr 1
    rw [← cancel_mono ((contractLeft A).obj X).iCycles, assoc π', ← h₂, ← assoc π', h₃,
      assoc a₃, Abelian.image.fac, assoc a₄, ShortComplex.toCycles_i]
    change a₄ ≫ kernel.ι _ ≫ X.map' 0 1 = _
    rw [kernel.lift_ι_assoc]
  rw [← cancel_epi π, ← cancel_epi π', ← h₄]
  simp

instance contractNatTrans_epi (X : ComposableArrows A 2) :
    Epi (ShortComplex.homologyMap ((contractNatTrans A).app X)) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A₀ a₀
  obtain ⟨A₁, π, _, a₁, h₁⟩ := (epi_iff_surjective_up_to_refinements
    ((contractRight A).obj X).homologyπ).mp inferInstance a₀
  have zero : (a₁ ≫ ((contractRight A).obj X).iCycles ≫ ((contractLeft A).obj X).g) ≫
      ((contractNatTrans A).app X).τ₃ = 0 := by
    rw [assoc, assoc, ← ((contractNatTrans A).app X).comm₂₃]
    change _ ≫ _ ≫ 𝟙 _ ≫ _ = 0
    simp
  set a₂ : A₁ ⟶ Abelian.image (X.map' 0 1 ≫ X.map' 1 2) :=
    kernel.lift (cokernel.π _) (a₁ ≫ ((contractRight A).obj X).iCycles ≫
    ((contractLeft A).obj X).g)
    (by dsimp [contractNatTrans, contractLeftToRight] at zero; erw [id_comp] at zero; exact zero)
  have h₂ : a₂ ≫ Abelian.image.ι _ = a₁ ≫ ((contractRight A).obj X).iCycles ≫
      ((contractLeft A).obj X).g := by simp [a₂]
  obtain ⟨A₃, π', _, a₃, h₃⟩ := (epi_iff_surjective_up_to_refinements
    (Abelian.factorThruImage (X.map' 0 1 ≫ X.map' 1 2))).mp inferInstance a₂
  set a₁' := π' ≫ a₁ ≫ ((contractRight A).obj X).iCycles - a₃ ≫ ((contractRight A).obj X).f
  have zero' : a₁' ≫ ((contractLeft A).obj X).g = 0 := by
    simp only [Preadditive.sub_comp, assoc, a₁']
    change _ - a₃ ≫ X.map' 0 1 ≫ X.map' 1 2 = 0
    rw [← Abelian.image.fac (X.map' 0 1 ≫ X.map' 1 2), ← assoc a₃, ← h₃, assoc π', h₂]
    dsimp [contractRight]
    simp
  set a₂' : A₃ ⟶ ((contractLeft A).obj X).cycles :=
    ((contractLeft A).obj X).liftCycles a₁' zero'
  have h₂' : a₂' ≫ ((contractLeft A).obj X).iCycles = a₁' := by simp [a₂']
  have eq : (a₂' ≫ ((contractLeft A).obj X).homologyπ) ≫
      ShortComplex.homologyMap ((contractNatTrans A).app X) = (π' ≫ π) ≫ a₀ := by
    rw [assoc, ShortComplex.homologyπ_naturality]
    have : a₂' ≫ ShortComplex.cyclesMap ((contractNatTrans A).app X) =
        π' ≫ a₁ - a₃ ≫ ((contractRight A).obj X).toCycles := by
      rw [← cancel_mono ((contractRight A).obj X).iCycles]
      simp only [assoc, ShortComplex.cyclesMap_i, Preadditive.sub_comp, ShortComplex.toCycles_i]
      rw [← assoc a₂', h₂']
      simp only [Preadditive.sub_comp, assoc, a₁']
      change _ ≫ _ ≫ _ ≫ 𝟙 _ - _ ≫ _ ≫ 𝟙 _ = _
      rw [comp_id, comp_id]
    rw [← assoc a₂', this, Preadditive.sub_comp, assoc π' a₁, ← h₁]
    simp
  exact ⟨A₃, π' ≫ π, inferInstance, a₂' ≫ ((contractLeft A).obj X).homologyπ, eq.symm⟩

instance contractNatTrans_iso (X : ComposableArrows A 2) :
    IsIso (ShortComplex.homologyMap ((contractNatTrans A).app X)) :=
  isIso_of_mono_of_epi _

lemma comp_contractNatTrans {X Y : ComposableArrows A 2} (u : X ⟶ Y) :
    (contractLeft A).map u ≫ (contractNatTrans A).app Y = contractLeftToRight u := by
  ext
  ·  dsimp [contractNatTrans, contractLeftToRight, contractLeft]; simp
  ·  dsimp [contractNatTrans, contractLeftToRight, contractLeft]; simp
  ·  dsimp [contractNatTrans, contractLeftToRight, contractLeft]; simp

lemma contractNatTrans_comp {X Y : ComposableArrows A 2} (u : X ⟶ Y) :
    (contractNatTrans A).app X ≫ (contractRight A).map u = contractLeftToRight u := by
  ext
  ·  dsimp [contractNatTrans, contractLeftToRight, contractRight]; simp
  ·  dsimp [contractNatTrans, contractLeftToRight, contractRight]; erw [id_comp]
  ·  dsimp [contractNatTrans, contractLeftToRight, contractRight]; erw [id_comp]; simp

end Contract

section LiftAbelian

noncomputable def homologyNatIso : homologyLeft A ≅ homologyRight A := by
  refine NatIso.ofComponents
    (fun X ↦ asIso (ShortComplex.homologyMap ((contractNatTrans A).app X))) (fun f ↦ ?_)
  dsimp [homologyLeft, homologyRight]
  simp [← ShortComplex.homologyMap_comp]

lemma homologyLeft_map_eq_of_homotopic (X Y : ComposableArrows A 2) (u v : X ⟶ Y)
    (h : homotopic u v) : (homologyLeft A).map u = (homologyLeft A).map v := by
  rw [← cancel_mono (ShortComplex.homologyMap ((contractNatTrans A).app Y))]
  simp only [Functor.comp_map, homologyLeft, ShortComplex.homologyFunctor_map]
  rw [← ShortComplex.homologyMap_comp, comp_contractNatTrans,
    ← ShortComplex.homologyMap_comp, comp_contractNatTrans]
  obtain ⟨σ₁, σ₂, eq⟩ := h
  refine ShortComplex.Homotopy.homologyMap_congr
    {h₀ := ?_, h₀_f := ?_, h₁ := σ₁, h₂ := σ₂, h₃ := ?_,
     g_h₃ := ?_, comm₁ := ?_, comm₂ := ?_, comm₃ := ?_}
  · exact kernel.ι _ ≫ (u.app zero - v.app zero - X.map' 0 1 ≫ σ₁)
  · dsimp [contractRight] at eq ⊢
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, assoc]
    rw [← u.naturality, eq]
    simp only [Nat.reduceAdd, Preadditive.comp_add,
      NatTrans.naturality, add_sub_cancel_right, add_sub_cancel_left]
    rw [← assoc _ _ σ₂, kernel.condition_assoc, zero_comp]
  · exact (u.app two - v.app two - σ₂ ≫ Y.map' 1 2) ≫ cokernel.π _
  · dsimp [contractLeft, two] at eq ⊢
    simp only [Preadditive.sub_comp, assoc, Preadditive.comp_sub]
    rw [u.naturality_assoc, eq]
    simp only [Nat.reduceAdd, Preadditive.add_comp, assoc, NatTrans.naturality_assoc,
      add_sub_cancel_right]
    conv_lhs => congr; rfl; rw [← assoc, cokernel.condition]
    rw [comp_zero]
  · dsimp [contractLeftToRight, contractLeft]
    simp
  · dsimp [contractLeftToRight, contractLeft, contractRight] at eq ⊢
    rw [eq]
    abel
  · dsimp [contractLeftToRight, contractRight, two]
    simp

lemma homologyRight_map_eq_of_homotopic (X Y : ComposableArrows A 2) (u v : X ⟶ Y)
    (h : homotopic u v) : (homologyRight A).map u = (homologyRight A).map v := by
  rw [← cancel_mono (homologyNatIso.inv.app Y)]
  simp only [NatTrans.naturality, NatIso.cancel_natIso_inv_left]
  exact homologyLeft_map_eq_of_homotopic X Y u v h

variable (A)

noncomputable def homologyLeftAbelian : Adel A ⥤ A :=
  Quotient.lift _ (homologyLeft A) homologyLeft_map_eq_of_homotopic

noncomputable def homologyRightAbelian : Adel A ⥤ A :=
  Quotient.lift _ (homologyRight A) homologyRight_map_eq_of_homotopic

noncomputable def homologyIsoAbelian : homologyLeftAbelian A ≅ homologyRightAbelian A :=
  Quotient.natIsoLift _ (Quotient.lift.isLift _ (homologyLeft A) homologyLeft_map_eq_of_homotopic
  ≪≫ homologyNatIso ≪≫ (Quotient.lift.isLift _ (homologyRight A)
  homologyRight_map_eq_of_homotopic).symm)

noncomputable def quotient_homologyLeftAbelian : quotient A ⋙ homologyLeftAbelian A ≅ homologyLeft A :=
  Quotient.lift.isLift _ _ _

noncomputable def quotient_homologyRightAbelian : quotient A ⋙ homologyRightAbelian A ≅ homologyRight A :=
  Quotient.lift.isLift _ _ _

instance : (homologyLeftAbelian A).Additive := Quotient.lift_additive _ _ _ _

instance : (homologyRightAbelian A).Additive := Quotient.lift_additive _ _ _ _

noncomputable def functor_homologyLeftAbelian : functor A ⋙ homologyLeftAbelian A ≅ 𝟭 A := by
  refine Functor.associator _ _ _ ≪≫ isoWhiskerLeft (functor_aux A) (Quotient.lift.isLift _ _ _)
    ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (functor_contractLeft A)
    (ShortComplex.homologyFunctor A) ≪≫ functor_aux_homology A

end LiftAbelian

end Adel

end CategoryTheory
