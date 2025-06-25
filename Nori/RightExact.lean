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

end RightExact

section Lift

variable (A)

--def lift : Adel C ⥤ A := sorry

end Lift

end Adel

end CategoryTheory
