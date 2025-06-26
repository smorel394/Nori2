import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Nori.LiftAbelian

universe u v u' v'

open CategoryTheory Category Functor Limits

open scoped ZeroObject

variable {A : Type u'} [Category.{v'} A] [Abelian A]

--variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] (F : C ⥤ A) [F.Additive]

namespace CategoryTheory

namespace Adel

namespace RightExact

open CandidateCoker

variable {X Y : ComposableArrows A 2} (u : X ⟶ Y)

instance : IsIso (ShortComplex.cyclesMap ((contractLeft A).map (candπ u))) where
  out := by
    set h := ((contractLeft A).obj (candcoker u)).leftHomologyData
    set h' := ((contractLeft A).obj Y).leftHomologyData
    use KernelFork.mapOfIsLimit (KernelFork.ofι h.i h.wi) h'.hi (Arrow.homMk biprod.fst biprod.fst
      (by change biprod.fst ≫ Y.map' 1 2 = biprod.map (Y.map' 1 2) (𝟙 (X.obj two)) ≫ biprod.fst
          simp))
    refine ⟨?_, ?_⟩
    · ext
      rw [id_comp, assoc]
      erw [KernelFork.mapOfIsLimit_ι]
      simp only [Fork.ofι_pt, const_obj_obj, parallelPair_obj_zero, Arrow.mk_left, Fork.ι_ofι,
        Arrow.homMk_left]
      change ShortComplex.cyclesMap' _ h' h ≫ _ = _
      rw [ShortComplex.cyclesMap'_i_assoc]
      change h'.i ≫ biprod.inl ≫ _ = _
      erw [biprod.inl_fst]
      rw [comp_id]
      rfl
    · ext
      rw [id_comp, assoc, ShortComplex.cyclesMap_i]
      erw [KernelFork.mapOfIsLimit_ι_assoc]
      simp only [Fork.ofι_pt, parallelPair_obj_zero, Fork.ι_ofι, Arrow.homMk_left]
      change _ ≫ _ ≫ biprod.inl = _
      ext
      · simp only [assoc, BinaryBicone.inl_fst, comp_id]
        rfl
      · simp only [assoc, BinaryBicone.inl_snd, comp_zero]
        have eq : (biprod.snd : ((contractLeft A).obj (candcoker u)).X₂ ⟶ X.obj two) =
            ((contractLeft A).obj (candcoker u)).g ≫ biprod.snd := by
          change _ = biprod.map (Y.map' 1 2) (𝟙 (X.obj two)) ≫ biprod.snd
          rw [biprod.map_snd, comp_id]
        erw [eq]
        simp

lemma cyclesMap_inv_iCycle : inv (ShortComplex.cyclesMap ((contractLeft A).map (candπ u))) ≫
    ((contractLeft A).obj Y).iCycles = ((contractLeft A).obj (candcoker u)).iCycles ≫ biprod.fst := by
  rw [← cancel_epi (ShortComplex.cyclesMap ((contractLeft A).map (candπ u))), IsIso.hom_inv_id_assoc,
    ShortComplex.cyclesMap_i_assoc]
  change _ = _ ≫ biprod.inl ≫ _
  erw [biprod.inl_fst]
  rw [comp_id]

@[reassoc]
lemma image_snd : kernel.ι ((candcoker u).map' 0 1 ≫ (candcoker u).map' 1 2) ≫
    biprod.snd ≫ X.map' 1 2 = 0 := by
  have : kernel.ι ((candcoker u).map' 0 1 ≫ (candcoker u).map' 1 2) ≫ ((candcoker u).map' 0 1 ≫
      (candcoker u).map' 1 2) ≫ biprod.snd = 0 := by
    rw [← assoc _ _ biprod.snd]
    convert zero_comp
    exact kernel.condition _
  change _ ≫ ((biprod.map (Y.map' 0 1) (X.map' 1 2) + biprod.snd ≫ u.app one ≫ biprod.inl) ≫
    biprod.map (Y.map' 1 2) (𝟙 (X.obj two))) ≫ biprod.snd = 0 at this
  simp only [Preadditive.add_comp, assoc, biprod.inl_map, biprod.map_snd, comp_id,
    BinaryBicone.inl_snd, comp_zero, add_zero] at this
  exact this

@[reassoc]
lemma image_fst : kernel.ι ((candcoker u).map' 0 1 ≫ (candcoker u).map' 1 2) ≫
    biprod.fst ≫ Y.map' 0 1 ≫ Y.map' 1 2 = 0 := by
  have : kernel.ι ((candcoker u).map' 0 1 ≫ (candcoker u).map' 1 2) ≫ ((candcoker u).map' 0 1 ≫
      (candcoker u).map' 1 2) ≫ biprod.fst = 0 := by
    rw [← assoc _ _ biprod.fst]
    convert zero_comp
    exact kernel.condition _
  change _ ≫ ((biprod.map (Y.map' 0 1) (X.map' 1 2) + biprod.snd ≫ u.app one ≫ biprod.inl) ≫
    biprod.map (Y.map' 1 2) (𝟙 (X.obj two))) ≫ biprod.fst = 0 at this
  simp only [Preadditive.add_comp, assoc, biprod.inl_map, biprod.map_fst, BinaryBicone.inl_fst,
    comp_id, Preadditive.comp_add] at this
  rw [biprod.map_fst_assoc, ← u.naturality, image_snd_assoc, zero_comp, add_zero] at this
  exact this

lemma liftCycles_homology : ((contractLeft A).obj Y).liftCycles (kernel.ι _ ≫ biprod.fst ≫ Y.map' 0 1)
    (by simp only [assoc]; exact image_fst u) ≫ ((contractLeft A).obj Y).homologyπ = 0 := by
  have eq : ((contractLeft A).obj Y).liftCycles (kernel.ι _ ≫ biprod.fst ≫ Y.map' 0 1)
      (by simp only [assoc]; exact image_fst u) = kernel.lift (Y.map' 0 1 ≫ Y.map' 1 2)
      (kernel.ι _ ≫ biprod.fst) (by simp only [assoc]; exact image_fst _) ≫
      ((contractLeft A).obj Y).toCycles := by
    rw [← cancel_mono ((contractLeft A).obj Y).iCycles]
    simp only [ShortComplex.liftCycles_i, assoc, ShortComplex.toCycles_i]
    change _ = _ ≫ (kernel.ι _ ≫ _)
    rw [kernel.lift_ι_assoc, assoc]
  rw [eq]
  simp

lemma toCycles_cyclesMap_inv_eq : ((contractLeft A).obj (candcoker u)).toCycles ≫
    inv (ShortComplex.cyclesMap ((contractLeft A).map (candπ u))) =
    ((contractLeft A).obj Y).liftCycles (kernel.ι _ ≫ biprod.fst ≫ Y.map' 0 1)
    (by simp only [assoc]; exact image_fst u)
    + ((contractLeft A).obj Y).liftCycles (kernel.ι _ ≫ biprod.snd ≫ u.app one)
    (by simp only [assoc]; erw [← u.naturality]; rw [image_snd_assoc, zero_comp]) := by
  rw [← cancel_mono ((contractLeft A).obj Y).iCycles, assoc]
  rw [cyclesMap_inv_iCycle, ← assoc, ShortComplex.toCycles_i]
  conv_lhs => dsimp [contractLeft]
  simp only [Preadditive.comp_add, Preadditive.add_comp, assoc]
  rw [biprod.map_fst, biprod.inl_fst, comp_id]
  simp only [ShortComplex.liftCycles_i]
  rfl

instance : Epi ((homologyLeft A).map (candπ u)) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A₀ a₀
  obtain ⟨A₁, π, _, a₁, h₁⟩ := (epi_iff_surjective_up_to_refinements ((contractLeft A).obj
    (candcoker u)).homologyπ).mp inferInstance a₀
  use A₁, π, inferInstance
  use a₁ ≫ inv (ShortComplex.cyclesMap ((contractLeft A).map (candπ u))) ≫
    ((contractLeft A).obj Y).homologyπ
  rw [h₁]
  simp only [assoc]
  congr 1
  rw [← cancel_epi (ShortComplex.cyclesMap ((contractLeft A).map (candπ u))),
    IsIso.hom_inv_id_assoc]
  exact (ShortComplex.homologyπ_naturality _).symm

lemma homology_comp_zero : (homologyLeft A).map u ≫ (homologyLeft A).map (candπ u) = 0 := by
  rw [← Functor.map_comp, ← (homologyLeft A).map_zero]
  exact homologyLeft_map_eq_of_homotopic _ _ _ _ (candcondition u)

lemma exact : (ShortComplex.mk _ _ (homology_comp_zero u)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ a₀ h₀
  dsimp at a₀ h₀
  obtain ⟨A₁, π, _, a₁, h₁⟩ := (epi_iff_surjective_up_to_refinements
    ((contractLeft A).obj Y).homologyπ).mp inferInstance a₀
  set S := ShortComplex.mk ((contractLeft A).obj (candcoker u)).toCycles ((contractLeft A).obj
    (candcoker u)).homologyπ ((contractLeft A).obj (candcoker u)).toCycles_comp_homologyπ
  obtain ⟨A₂, π', _, a₂, h₂⟩ := S.exact_iff_exact_up_to_refinements.mp
    (S.exact_of_g_is_cokernel ((contractLeft A).obj (candcoker u)).homologyIsCokernel)
    (a₁ ≫ ShortComplex.cyclesMap ((contractLeft A).map (candπ u)))
    (by rw [assoc, ← ShortComplex.homologyπ_naturality, ← assoc a₁, ← h₁, assoc]
        convert comp_zero)
  have h₂' : (a₂ ≫ kernel.ι _ ≫ biprod.snd) ≫ ((contractLeft A).obj X).g = 0 := by
    change _ ≫ X.map' 1 2 = 0
    simp only [assoc]
    rw [image_snd, comp_zero]
  use A₂, π' ≫ π, inferInstance, ((contractLeft A).obj X).liftCycles _ h₂' ≫
    ((contractLeft A).obj X).homologyπ
  simp only [homologyLeft, comp_obj, ShortComplex.homologyFunctor_obj, Functor.comp_map,
    ShortComplex.homologyFunctor_map, assoc, ShortComplex.homologyπ_naturality]
  apply_fun (fun x ↦ x ≫ inv (ShortComplex.cyclesMap ((contractLeft A).map (candπ u)))) at h₂
  rw [assoc, assoc, IsIso.hom_inv_id, comp_id] at h₂
  rw [h₁, ← assoc, h₂, assoc a₂, toCycles_cyclesMap_inv_eq, Preadditive.comp_add,
    Preadditive.add_comp, assoc, liftCycles_homology, comp_zero, zero_add, ← assoc _ (ShortComplex.cyclesMap _)]
  congr 1
  rw [← cancel_mono ((contractLeft A).obj Y).iCycles]
  simp only [assoc, ShortComplex.liftCycles_i, ShortComplex.liftCycles_comp_cyclesMap]
  rfl

section Preserves

noncomputable def preservesCokernels_aux : IsColimit ((homologyLeftAbelian A).mapCocone ((Cocones.precompose
    (compNatIso' (quotient A)).inv).obj (cocone_aux u))) := by
  have := (ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).mp ⟨RightExact.exact u, inferInstance⟩
  dsimp at this
  set α : parallelPair ((quotient A).map u) 0 ⋙ homologyLeftAbelian A ≅
      parallelPair ((homologyLeft A).map u) 0 := by
    refine parallelPair.ext ((quotient_homologyLeftAbelian A).app X) ((quotient_homologyLeftAbelian A).app Y) ?_ ?_
    · dsimp; rw [← (quotient_homologyLeftAbelian A).hom.naturality]; rfl
    · dsimp; simp
  refine (IsColimit.equivOfNatIsoOfIso α _ _ ?_).invFun (Classical.choice this)
  refine Cocones.ext (Iso.refl _) (fun j ↦ ?_)
  match j with
  | WalkingParallelPair.zero =>
    dsimp [α, compNatIso', cocone_aux]
    rw [← cancel_epi ((quotient_homologyLeftAbelian A).hom.app X)]
    simp only [comp_obj, id_comp, comp_id, Iso.hom_inv_id_app_assoc]
    conv_rhs => rw [← Functor.map_comp, ← (quotient_homologyLeftAbelian A).hom.naturality]
    convert (comp_id _).symm
  | WalkingParallelPair.one =>
    dsimp [α, compNatIso', cocone_aux]
    rw [← cancel_epi ((quotient_homologyLeftAbelian A).hom.app Y)]
    simp only [comp_obj, id_comp, comp_id, Iso.hom_inv_id_app_assoc]
    rw [← (quotient_homologyLeftAbelian A).hom.naturality]
    convert (comp_id _).symm

def preservesCokernelsComposableArrows : PreservesColimit (parallelPair ((quotient A).map u) 0)
    (homologyLeftAbelian A) where
  preserves hc := by
    set e := hc.uniqueUpToIso ((IsColimit.precomposeHomEquiv (compNatIso' (quotient A)).symm
      (cocone_aux u)).invFun (cocone_isColimit u))
    have h : IsColimit ((homologyLeftAbelian A).mapCocone ((Cocones.precompose (compNatIso'
      (quotient A)).inv).obj (cocone_aux u))) := preservesCokernels_aux u
    exact Nonempty.intro (h.ofIsoColimit ((Cocones.functoriality _ (homologyLeftAbelian A)).mapIso e).symm)

instance {X Y : Adel A} (u : X ⟶ Y) : PreservesColimit (parallelPair u 0) (homologyLeftAbelian A) :=
  preservesCokernels_of_preservesCokernelsComposableArrows (homologyLeftAbelian A)
  preservesCokernelsComposableArrows u

end Preserves

end RightExact

/-
The morally correct way to do would be to use opposite categories.
-/
namespace LeftExact

open CandidateKer

variable {X Y : ComposableArrows A 2} (u : X ⟶ Y)

instance : IsIso (ShortComplex.opcyclesMap ((contractRight A).map (candι u))) where
  out := by
    set h := ((contractRight A).obj (candker u)).rightHomologyData
    set h' := ((contractRight A).obj X).rightHomologyData
    use CokernelCofork.mapOfIsColimit h'.hp (CokernelCofork.ofπ h.p h.wp)
      (Arrow.homMk biprod.inl biprod.inl
      (by change biprod.inl ≫ biprod.map (X.map' 0 1) (𝟙 (Y.obj zero)) = X.map' 0 1 ≫ biprod.inl
          simp))
    refine ⟨?_, ?_⟩
    · ext
      rw [comp_id, ShortComplex.p_opcyclesMap_assoc]
      erw [CokernelCofork.π_mapOfIsColimit h'.hp (CokernelCofork.ofπ h.p h.wp)]
      simp only [ Arrow.mk_right, Cofork.ofπ_pt, const_obj_obj, Arrow.mk_left,
        Arrow.homMk_right, Cofork.π_ofπ]
      change biprod.fst ≫ _ = h.p
      ext
      · rw [biprod.inl_fst_assoc]
        rfl
      · rw [biprod.inr_fst_assoc, zero_comp]
        have eq : biprod.inr = biprod.inr ≫ ((contractRight A).obj (candker u)).f := by
          change _ = _ ≫ biprod.map _ _
          rw [biprod.inr_map, id_comp]
        rw [eq]
        simp
    · ext
      rw [comp_id]
      erw [CokernelCofork.π_mapOfIsColimit_assoc h'.hp (CokernelCofork.ofπ h.p h.wp)]
      simp only [Arrow.mk_right, Arrow.mk_left, Arrow.homMk_right, Cofork.ofπ_pt, Cofork.π_ofπ]
      change _ ≫ ((contractRight A).obj (candker u)).pOpcycles ≫ _ = _
      rw [ShortComplex.p_opcyclesMap]
      change _ ≫ biprod.fst ≫ _ = _
      conv_lhs => erw [biprod.inl_fst_assoc]

@[reassoc]
lemma pOpcycles_opcyclesMap_inv :
    ((contractRight A).obj X).pOpcycles ≫ inv (ShortComplex.opcyclesMap ((contractRight A).map
    (candι u))) = biprod.inl ≫ ((contractRight A).obj (candker u)).pOpcycles := by
  rw [← cancel_mono (ShortComplex.opcyclesMap ((contractRight A).map (candι u))), assoc,
    IsIso.inv_hom_id, comp_id, assoc, ShortComplex.p_opcyclesMap]
  change _ = _ ≫ biprod.fst ≫ _
  erw [biprod.inl_fst_assoc]

@[reassoc]
lemma inr_image : Y.map' 0 1 ≫ biprod.inr ≫ cokernel.π
    ((candker u).map' 0 1 ≫ (candker u).map' 1 2) = 0 := by
  have : biprod.inr ≫ ((candker u).map' 0 1 ≫ (candker u).map' 1 2) ≫
      cokernel.π ((candker u).map' 0 1 ≫ (candker u).map' 1 2) = 0 := by
    rw [cokernel.condition, comp_zero]
  change biprod.inr ≫ (biprod.map (X.map' 0 1) (𝟙 (Y.obj zero)) ≫
    (biprod.map (X.map' 1 2) (Y.map' 0 1) + biprod.fst ≫ u.app one ≫ biprod.inr)) ≫ _ = 0 at this
  simp only [Preadditive.comp_add, biprod.map_fst_assoc, NatTrans.naturality_assoc,
    Preadditive.add_comp, assoc, biprod.inr_map_assoc, id_comp, BinaryBicone.inr_fst_assoc,
    zero_comp, add_zero] at this
  exact this

@[reassoc]
lemma inl_image : X.map' 0 1 ≫ X.map' 1 2 ≫ biprod.inl ≫
    cokernel.π ((candker u).map' 0 1 ≫ (candker u).map' 1 2) = 0 := by
  have : biprod.inl ≫ ((candker u).map' 0 1 ≫ (candker u).map' 1 2) ≫
      cokernel.π ((candker u).map' 0 1 ≫ (candker u).map' 1 2) = 0 := by
    rw [cokernel.condition, comp_zero]
  change biprod.inl ≫ (biprod.map (X.map' 0 1) (𝟙 (Y.obj zero)) ≫
    (biprod.map (X.map' 1 2) (Y.map' 0 1) + biprod.fst ≫ u.app one ≫ biprod.inr)) ≫ _ = 0 at this
  simp only [Preadditive.comp_add, biprod.map_fst_assoc, NatTrans.naturality_assoc,
    Preadditive.add_comp, assoc, biprod.inl_map_assoc, BinaryBicone.inl_fst_assoc] at this
  rw [inr_image, comp_zero, add_zero] at this
  exact this

lemma homology_descOpcycles : ((contractRight A).obj X).homologyι ≫
    ((contractRight A).obj X).descOpcycles (X.map' 1 2 ≫ biprod.inl ≫ cokernel.π _)
    (inl_image u) = 0 := by
  have eq : ((contractRight A).obj X).descOpcycles (X.map' 1 2 ≫ biprod.inl ≫ cokernel.π _)
    (inl_image u) = ((contractRight A).obj X).fromOpcycles ≫ cokernel.desc (X.map' 0 1 ≫
    X.map' 1 2) (biprod.inl ≫ cokernel.π _) (by simp only [assoc]; exact inl_image u) := by
    rw [← cancel_epi ((contractRight A).obj X).pOpcycles]
    simp only [ShortComplex.p_descOpcycles, ShortComplex.p_fromOpcycles_assoc]
    change _ = (_ ≫ cokernel.π (X.map' 0 1 ≫ X.map' 1 2)) ≫ _
    rw [assoc, cokernel.π_desc]
  rw [eq]
  simp

lemma toCycles_cyclesMap_inv_eq : inv (ShortComplex.opcyclesMap ((contractRight A).map (candι u)))
    ≫ ((contractRight A).obj (candker u)).fromOpcycles =
    ((contractRight A).obj X).descOpcycles (X.map' 1 2 ≫ biprod.inl ≫ cokernel.π _)
    (inl_image u)
    + ((contractRight A).obj X).descOpcycles (u.app one ≫ biprod.inr ≫ cokernel.π _)
    (by erw [u.naturality_assoc]; rw [inr_image, comp_zero]) := by
  rw [← cancel_epi ((contractRight A).obj X).pOpcycles]
  rw [pOpcycles_opcyclesMap_inv_assoc, ShortComplex.p_fromOpcycles]
  conv_lhs => dsimp [contractRight]
  simp only [Preadditive.comp_add, Preadditive.add_comp, assoc]
  rw [biprod.inl_map_assoc, biprod.inl_fst_assoc]
  simp only [ShortComplex.p_descOpcycles]
  rfl

instance : Mono ((homologyRight A).map (candι u)) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro A₀ a₀ h₀
  dsimp [homologyRight] at h₀
  refine (Preadditive.mono_iff_cancel_zero ((contractRight A).obj (candker u)).homologyι).mp
    inferInstance A₀ a₀ ?_
  rw [← cancel_mono (ShortComplex.opcyclesMap ((contractRight A).map (candι u))), zero_comp]
  rw [assoc, ← ShortComplex.homologyι_naturality, ← assoc, h₀, zero_comp]

lemma homology_comp_zero : (homologyRight A).map (candι u) ≫ (homologyRight A).map u = 0 := by
  rw [← Functor.map_comp, ← (homologyRight A).map_zero]
  exact homologyRight_map_eq_of_homotopic _ _ _ _ (candcondition u)

lemma exact : (ShortComplex.mk _ _ (homology_comp_zero u)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ a₀ h₀
  dsimp at a₀ h₀
  set a₁ := a₀ ≫ ((contractRight A).obj X).homologyι with ha₁
  have : a₁ ≫ inv (ShortComplex.opcyclesMap ((contractRight A).map (candι u))) ≫
      ((contractRight A).obj (candker u)).fromOpcycles = 0 := by
    rw [toCycles_cyclesMap_inv_eq, Preadditive.comp_add]
    conv_lhs => congr; rw [ha₁, assoc, homology_descOpcycles, comp_zero]
    rw [zero_add]
    obtain ⟨A₁, π, _, a₁', h₁'⟩ := (epi_iff_surjective_up_to_refinements
      ((contractRight A).obj X).pOpcycles).mp inferInstance a₁
    rw [← cancel_epi π, ← assoc π a₁, h₁', assoc, ShortComplex.p_descOpcycles, comp_zero]
    have h₁'' : (a₁' ≫ u.app one) ≫ ((contractRight A).obj Y).pOpcycles = 0 := by
      change (a₁' ≫ ((contractRight A).map u).τ₂) ≫ _ = 0
      rw [assoc, ← ShortComplex.p_opcyclesMap, ← assoc, ← h₁', ha₁, assoc, assoc,
        ← ShortComplex.homologyι_naturality, ← assoc a₀]
      erw [h₀]
      simp
    set S := ShortComplex.mk (Y.map' 0 1) ((contractRight A).obj Y).pOpcycles
      ((contractRight A).obj Y).f_pOpcycles
    obtain ⟨A₂, π', _, a₂, h₂⟩ := S.exact_iff_exact_up_to_refinements.mp (S.exact_of_g_is_cokernel
      ((contractRight A).obj Y).opcyclesIsCokernel) (a₁' ≫ u.app one) h₁''
    rw [← cancel_epi π', reassoc_of% h₂, inr_image, comp_zero, comp_zero]
  set a₂ := ((contractRight A).obj (candker u)).liftHomology (a₁ ≫ inv (ShortComplex.opcyclesMap
    ((contractRight A).map (candι u)))) (by rw [assoc, this])
  use A₀, 𝟙 _, inferInstance, a₂
  change _ = _ ≫ (homologyRight A).map (candι u)
  rw [id_comp, ← cancel_mono ((contractRight A).obj X).homologyι, assoc]
  dsimp [homologyRight]
  rw [ShortComplex.homologyι_naturality, ← ha₁]
  change _ = a₂ ≫ ((contractRight A).obj (candker u)).homologyι ≫ _
  rw [← assoc, ShortComplex.liftHomology_ι, assoc, IsIso.inv_hom_id, comp_id]

section Preserves

noncomputable def preservesKernels_aux : IsLimit ((homologyRightAbelian A).mapCone ((Cones.postcompose
    (compNatIso' (quotient A)).hom).obj (cone_aux u))) := by
  have := (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).mp ⟨LeftExact.exact u, inferInstance⟩
  dsimp at this
  set α : parallelPair ((quotient A).map u) 0 ⋙ homologyRightAbelian A ≅
      parallelPair ((homologyRight A).map u) 0 := by
    refine parallelPair.ext ((quotient_homologyRightAbelian A).app X)
      ((quotient_homologyRightAbelian A).app Y) ?_ ?_
    · dsimp; rw [← (quotient_homologyRightAbelian A).hom.naturality]; rfl
    · dsimp; simp
  refine (IsLimit.equivOfNatIsoOfIso α _ _ ?_).invFun (Classical.choice this)
  refine Cones.ext (Iso.refl _) (fun j ↦ ?_)
  match j with
  | WalkingParallelPair.zero =>
    dsimp [α, compNatIso', cone_aux]
    rw [← cancel_mono ((quotient_homologyRightAbelian A).inv.app X)]
    simp only [comp_obj, comp_id, assoc,
      Iso.hom_inv_id_app, id_comp, NatTrans.naturality, Functor.comp_map]
    conv_rhs => erw [← (quotient_homologyRightAbelian A).inv.naturality]
    convert (comp_id _).symm
  | WalkingParallelPair.one =>
    dsimp [α, compNatIso', cone_aux]
    rw [← cancel_mono ((quotient_homologyRightAbelian A).inv.app Y)]
    simp only [comp_obj, comp_id, map_comp, assoc,
      Iso.hom_inv_id_app, id_comp, NatTrans.naturality, Functor.comp_map, NatTrans.naturality_assoc]
    rw [← Functor.map_comp]; erw [← (quotient_homologyRightAbelian A).inv.naturality]
    convert (comp_id _).symm

lemma preservesKernelsComposableArrows :
    PreservesLimit (parallelPair ((quotient A).map u) 0) (homologyRightAbelian A) where
  preserves hc := by
    set e := hc.uniqueUpToIso ((IsLimit.postcomposeHomEquiv (compNatIso' (quotient A))
      (cone_aux u)).invFun (cone_isLimit u))
    have h : IsLimit ((homologyRightAbelian A).mapCone ((Cones.postcompose (compNatIso'
      (quotient A)).hom).obj (cone_aux u))) := preservesKernels_aux u
    exact Nonempty.intro (h.ofIsoLimit ((Cones.functoriality _ (homologyRightAbelian A)).mapIso e).symm)

instance {X Y : Adel A} (u : X ⟶ Y) : PreservesLimit (parallelPair u 0) (homologyRightAbelian A) :=
  preservesKernels_of_preservesKernelsComposableArrows (homologyRightAbelian A)
  preservesKernelsComposableArrows u

instance {X Y : Adel A} (u : X ⟶ Y) : PreservesLimit (parallelPair u 0) (homologyLeftAbelian A) :=
  preservesLimit_of_natIso (parallelPair u 0) (homologyIsoAbelian A).symm

end Preserves

end LeftExact

end Adel

end CategoryTheory
