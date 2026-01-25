import Nori.Functoriality

universe u v

open CategoryTheory Category Functor Limits Adel

open scoped ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

local instance : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C

namespace CategoryTheory

namespace Functor

section Calculs

open CandidateKer CandidateCoker

variable (C)

noncomputable def contract₁ :
    ComposableArrows C 2 ⥤ ComposableArrows C 2 where
  obj X := ComposableArrows.mk₂ (0 : 0 ⟶ X.obj zero) (X.map' 0 1 ≫ X.map' 1 2)
  map u := ComposableArrows.homMk₂ 0 (u.app zero) (u.app two)
    (by dsimp; simp) (by change (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
                         rw [assoc, u.naturality, u.naturality_assoc])
--  map_id X := by aesop_cat
--  map_comp _ _ := by aesop_cat

variable {C}

noncomputable def contract₁_iso_candker (X : ComposableArrows C 2) : (contract₁ C).obj X ≅
    candker ((functor_aux C).map (X.map' 0 1 ≫ X.map' 1 2)) := by
  refine ComposableArrows.isoMk₂ ?_ ?_ ?_ ?_ ?_
  · exact isoBiprodZero (isZero_zero _)
  · exact isoBiprodZero (isZero_zero _)
  · exact isoZeroBiprod (isZero_zero _)
  · dsimp [contract₁, functor_aux, functor_aux_complex]
    simp
  · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, Fin.zero_eta, Fin.reduceFinMk,
    ComposableArrows.map', homOfLE_leOfHom, ComposableArrows.obj', isoZeroBiprod_hom,
    isoBiprodZero_hom]
    change _ = _ ≫ (biprod.map _ _  + _)
    rw [Preadditive.comp_add, biprod.inl_map]
    erw [biprod.inl_fst_assoc]
    change _ = 0 ≫ _ + _ ≫ _
    rw [zero_comp, zero_add]
    rfl

noncomputable def contract₁_ι (X : ComposableArrows C 2) :
    (contract₁ C).obj X ⟶ (functor_aux C).obj (X.obj zero) :=
  ComposableArrows.homMk₂ 0 (𝟙 _) 0 (by change 0 ≫ _ = 0 ≫ _; simp)
  (by change _ ≫ 0 = _ ≫ 0; simp)

lemma contract₁_iso_candker_ι (X : ComposableArrows C 2) :
    (contract₁_iso_candker X).hom ≫ candι _ = contract₁_ι X := by
  dsimp [contract₁_iso_candker, contract₁, contract₁_ι]
  ext
  · dsimp
    erw [biprod.inl_fst]
    simp
  · dsimp
    erw [biprod.inl_fst]
  · dsimp
    change biprod.inr ≫ biprod.fst  = _
    rw [biprod.inr_fst]

noncomputable def contract₁_cone (X : ComposableArrows C 2) :
    KernelFork ((functor C).map (X.map' 0 1) ≫ (functor C).map (X.map' 1 2)) := by
  refine Fork.ofι ((quotient C).map (contract₁_ι X)) ?_
  suffices eq : (quotient C).map (contract₁_ι X ≫ _) = (quotient C).map 0 by
    dsimp at eq ⊢
    simp only [map_comp, Functor.map_zero, comp_zero] at eq ⊢
    exact eq
  rw [quotient_map_eq_iff]
  use 0, 𝟙 _
  dsimp [contract₁_ι]
  simp only [id_comp, zero_comp, zero_add, add_zero]
  erw [comp_id]
  rfl

noncomputable def contract₁_isKernel (X : ComposableArrows C 2) : IsLimit (contract₁_cone X) := by
  set α : parallelPair ((functor C).map (X.map' 0 1) ≫ (functor C).map (X.map' 1 2)) 0 ≅
      parallelPair ((quotient C).map ((functor_aux C).map (X.map' 0 1 ≫
      X.map' 1 2))) 0 := NatIso.ofComponents
    (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_|_|_) <;> simp [functor])
  refine (IsLimit.postcomposeHomEquiv α (contract₁_cone X)).toFun ((cone_isLimit _).ofIsoLimit ?_)
  refine Fork.ext ((quotient C).mapIso (contract₁_iso_candker X)).symm ?_
  · rw [← cancel_epi ((quotient C).mapIso (contract₁_iso_candker X)).hom, Iso.symm_hom,
      Iso.hom_inv_id_assoc]
    change _ ≫ 𝟙 _ = (quotient C).map _ ≫ (quotient C).map _
    rw [← (quotient C).map_comp, contract₁_iso_candker_ι X, comp_id]
    rfl

variable (C)

noncomputable def contract₂ : ComposableArrows C 2 ⥤ ComposableArrows C 2 :=
  (evaluation _ _).obj one ⋙ functor_aux C

noncomputable def contract₃ : ComposableArrows C 2 ⥤ ComposableArrows C 2 :=
  (evaluation _ _).obj two ⋙ functor_aux C

noncomputable def contract_f : contract₁ C ⟶ contract₂ C where
  app X := ComposableArrows.homMk₂ 0 (X.map' 0 1) 0 (by change 0 ≫ _ = _; simp)
    (by change _ = _ ≫ 0; simp)
  naturality _ _ u := by
    ext
    · dsimp; simp
    · change u.app zero ≫ _ = _ ≫ u.app one
      dsimp
      simp
    · change _ ≫ 0 = _ ≫ 0
      simp

noncomputable def contract_g : contract₂ C ⟶ contract₃ C where
  app X := ComposableArrows.homMk₂ 0 (X.map' 1 2) 0 (by change 0 ≫ _ = _; simp)
    (by change _ = _ ≫ 0; simp)
  naturality _ _ u := by
    ext
    · dsimp; simp
    · change u.app one ≫ _ = _ ≫ u.app two; erw [u.naturality]; rfl
    · change 0 ≫ _ = _ ≫ 0; simp

variable {C} in
lemma contract_zero (X : ComposableArrows C 2) :
    homotopic ((contract_f C).app X ≫ (contract_g C).app X) 0 := by
  use 0, 𝟙 _
  dsimp
  simp only [zero_comp, zero_add, add_zero]
  erw [comp_id]
  rfl

noncomputable def contract : ComposableArrows C 2 ⥤ ShortComplex (Adel C) where
  obj X := ShortComplex.mk ((quotient C).map ((contract_f C).app X)) ((quotient C).map
    ((contract_g C).app X))
    (by rw [← Functor.map_comp, ← (quotient C).map_zero, quotient_map_eq_iff]
        exact contract_zero X)
  map u := ShortComplex.homMk ((quotient C).map ((contract₁ C).map u)) ((quotient C).map
    ((contract₂ C).map u)) ((quotient C).map ((contract₃ C).map u))
    (by dsimp; rw [← Functor.map_comp, NatTrans.naturality, Functor.map_comp])
    (by dsimp; rw [← Functor.map_comp, NatTrans.naturality, Functor.map_comp])
  map_id X := by
    ext
    · dsimp; simp
    · dsimp; simp
    · dsimp; simp
  map_comp f g := by
    ext
    · dsimp; simp
    · dsimp; simp
    · dsimp; simp

noncomputable def contract_compat :
    (functor C).mapComposableArrows 2 ⋙ contractLeft (Adel C) ≅ contract C := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun {X Y} u ↦ ?_)
  · refine ShortComplex.isoMk ?_ ?_ ?_ ?_ ?_
    · exact ((kernelIsKernel _).conePointUniqueUpToIso (contract₁_isKernel X))
    · exact Iso.refl _
    · exact Iso.refl _
    · dsimp [contract]
      have eq : (contract_f C).app X = contract₁_ι X ≫ (functor_aux C).map (X.map' 0 1) := by
        dsimp [contract_f, contract₁_ι, functor_aux]
        ext
        · dsimp; rw [zero_comp]
        · dsimp; rw [id_comp]; rfl
        · change 0 = _ ≫ 0; rw [comp_zero]
      rw [eq, (quotient C).map_comp]
      change _ ≫ (contract₁_cone X).π.app WalkingParallelPair.zero ≫ _ = _
      rw [IsLimit.conePointUniqueUpToIso_hom_comp_assoc, comp_id]
      dsimp [contractLeft]
      rfl
    · dsimp
      simp only [id_comp, comp_id]
      rfl
  · ext
    · dsimp [contractLeft, contract]
      have : Mono ((contract₁_cone Y).π.app WalkingParallelPair.zero) :=
        mono_of_isLimit_fork (contract₁_isKernel Y)
      rw [← cancel_mono ((contract₁_cone Y).π.app WalkingParallelPair.zero)]
      have eq : (quotient C).map ((contract₁ C).map u) ≫
          (contract₁_cone Y).π.app WalkingParallelPair.zero =
          (contract₁_cone X).π.app WalkingParallelPair.zero ≫
          (functor C).map (u.app zero) := by
        change _ ≫ (quotient C).map _ = (quotient C).map _ ≫ (quotient C).map _
        rw [← (quotient C).map_comp, ← (quotient C).map_comp]
        congr 1
        dsimp [contract₁, contract₁_ι, functor_aux]
        ext
        · dsimp; rw [zero_comp, zero_comp]
        · dsimp; rw [id_comp, comp_id]; rfl
        · change _ ≫ 0 = 0 ≫ _; rw [zero_comp, comp_zero]
      simp only [assoc]
      rw [eq, IsLimit.conePointUniqueUpToIso_hom_comp_assoc,
        IsLimit.conePointUniqueUpToIso_hom_comp]
      dsimp
      rw [kernel.lift_ι]
    · dsimp
      rw [id_comp, comp_id]
      rfl
    · dsimp
      rw [comp_id, id_comp]
      rfl

noncomputable def cycles : ComposableArrows C 2 ⥤ ComposableArrows C 2 where
  obj X := ComposableArrows.mk₂ (0 : 0 ⟶ X.obj one) (X.map' 1 2)
  map {X Y} u := ComposableArrows.homMk₂ 0 (u.app one) (u.app two) (by simp)
    (u.naturality _)
  map_id X := by
    ext
    · dsimp; simp
    · dsimp
    · rfl
  map_comp _ _ := by
    ext
    · dsimp; simp
    · dsimp
    · rfl

noncomputable def tocycles : contract₁ C ⟶ cycles C where
  app X := ComposableArrows.homMk₂ 0 (X.map' 0 1) (𝟙 _) (by simp [contract₁])
    (by change _ ≫ 𝟙 _ = _; rw [comp_id]; rfl)
  naturality {_ _} u := by
    dsimp [cycles, contract₁]
    ext
    · dsimp
    · exact (u.naturality _).symm
    · change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [comp_id, id_comp]
      rfl

noncomputable def icycles : cycles C ⟶ contract₂ C where
  app X := ComposableArrows.homMk₂ 0 (𝟙 _) 0 (by dsimp; rw [comp_id, zero_comp]; rfl)
    (by dsimp; rw [comp_zero, id_comp]; rfl)
  naturality {_ _} u := by
    dsimp [cycles, contract₂]
    ext
    · dsimp; simp
    · dsimp
      rw [comp_id, id_comp]
      rfl
    · change _ ≫ 0 = 0 ≫ _
      rw [comp_zero, zero_comp]

lemma tocycles_i : tocycles C ≫ icycles C = contract_f C := by
  dsimp [tocycles, icycles, contract_f]
  ext
  · dsimp; simp
  · dsimp; simp
  · change _ ≫ 0 = 0; simp

variable {C}

noncomputable def cycles_iso_candker (X : ComposableArrows C 2) : (cycles C).obj X ≅
    candker ((contract_g C).app X) := by
  refine ComposableArrows.isoMk₂ ?_ ?_ ?_ ?_ ?_
  · exact isoBiprodZero (isZero_zero _)
  · exact isoBiprodZero (isZero_zero _)
  · exact isoZeroBiprod (isZero_zero _)
  · dsimp [cycles, contract_g, contract₂, functor_aux, functor_aux_complex]
    simp
  · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, Fin.zero_eta, Fin.reduceFinMk,
    ComposableArrows.map', homOfLE_leOfHom, ComposableArrows.obj', isoZeroBiprod_hom,
    isoBiprodZero_hom]
    change _ = _ ≫ (biprod.map _ _  + _)
    rw [Preadditive.comp_add, biprod.inl_map]
    erw [biprod.inl_fst_assoc]
    change _ = 0 ≫ _ + _ ≫ _
    rw [zero_comp, zero_add]
    rfl

lemma cycles_iso_candker_ι (X : ComposableArrows C 2) :
    (cycles_iso_candker X).hom ≫ candι ((contract_g C).app X) = (icycles C).app X := by
  dsimp [cycles_iso_candker, cycles, icycles, contract_g]
  ext
  · dsimp
    erw [biprod.inl_fst]
    simp
  · dsimp
    erw [biprod.inl_fst]
  · dsimp
    change biprod.inr ≫ biprod.fst  = _
    rw [biprod.inr_fst]

noncomputable def cycles_cone (X : ComposableArrows C 2) :
    KernelFork ((contract C).obj X).g := by
  refine Fork.ofι ((quotient C).map ((icycles C).app X)) ?_
  suffices eq : (quotient C).map ((icycles C).app X ≫ _) = (quotient C).map 0 by
    dsimp at eq ⊢
    simp only [map_comp, Functor.map_zero, comp_zero] at eq ⊢
    exact eq
  rw [quotient_map_eq_iff]
  use 0, 𝟙 _
  dsimp [icycles]
  simp only [id_comp, zero_comp, zero_add, add_zero]
  erw [comp_id]
  rfl

noncomputable def cycles_isKernel (X : ComposableArrows C 2) : IsLimit (cycles_cone X) := by
  refine (cone_isLimit _).ofIsoLimit ?_
  refine Fork.ext ((quotient C).mapIso (cycles_iso_candker X)).symm ?_
  rw [← cancel_epi ((quotient C).mapIso (cycles_iso_candker X)).hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]
  change _  = (quotient C).map _ ≫ (quotient C).map _
  rw [← (quotient C).map_comp, cycles_iso_candker_ι X]
  rfl

variable (C) in
noncomputable def cycles_iso_cycles :
    cycles C ⋙ quotient C ≅ contract C ⋙ ShortComplex.cyclesFunctor (Adel C) := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun {X Y} u ↦ ?_)
  · exact (cycles_isKernel X).conePointUniqueUpToIso ((contract C).obj X).cyclesIsKernel
  · dsimp
    rw [← cancel_mono ((contract C).obj Y).iCycles, assoc, assoc, ShortComplex.cyclesMap_i]
    erw [IsLimit.conePointUniqueUpToIso_hom_comp_assoc (cycles_isKernel X)
      ((contract C).obj X).cyclesIsKernel WalkingParallelPair.zero,
      IsLimit.conePointUniqueUpToIso_hom_comp (cycles_isKernel Y)
      ((contract C).obj Y).cyclesIsKernel WalkingParallelPair.zero]
    dsimp [cycles_cone, icycles, contract, cycles, contract₂]
    rw [← (quotient C).map_comp, ← (quotient C).map_comp]
    congr 1
    ext
    · dsimp; rw [zero_comp, zero_comp]
    · dsimp; rw [id_comp, comp_id]; rfl
    · change _ ≫ 0 = 0 ≫ _
      rw [zero_comp, comp_zero]

lemma cycles_iso_cycles_i (X : ComposableArrows C 2) :
    (cycles_iso_cycles C).hom.app X ≫ ((contract C).obj X).iCycles =
    (quotient C).map ((icycles C).app X) := by
  dsimp [cycles_iso_cycles]
  erw [IsLimit.conePointUniqueUpToIso_hom_comp (cycles_isKernel X)
    ((contract C).obj X).cyclesIsKernel WalkingParallelPair.zero]
  rfl

lemma to_cycles_iso_cycles_hom (X : ComposableArrows C 2) :
    (quotient C).map ((tocycles C).app X) ≫ (cycles_iso_cycles C).hom.app X =
    ((contract C).obj X).toCycles := by
  rw [← cancel_mono ((contract C).obj X).iCycles, assoc, cycles_iso_cycles_i,
    ShortComplex.toCycles_i]
  rw [← (quotient C).map_comp, ← NatTrans.comp_app, tocycles_i]
  rfl

lemma to_cycles_iso_cycles_inv (X : ComposableArrows C 2) :
    ((contract C).obj X).toCycles ≫ (cycles_iso_cycles C).inv.app X =
    (quotient C).map ((tocycles C).app X) := by
  rw [← cancel_mono ((cycles_iso_cycles C).hom.app X), assoc, Iso.inv_hom_id_app,
    to_cycles_iso_cycles_hom]
  erw [comp_id]

variable (C)

noncomputable def homology : ComposableArrows C 2 ⥤ ComposableArrows C 2 where
  obj X := ComposableArrows.mk₂ (biprod.lift (X.map' 0 1) (X.map' 0 1 ≫ X.map' 1 2))
    (biprod.map (X.map' 1 2) (𝟙 _))
  map {X Y} u := ComposableArrows.homMk₂ (u.app zero) (biprod.map (u.app one) (u.app two))
    (biprod.map (u.app two) (u.app two))
    (by dsimp
        refine biprod.hom_ext _ _ ?_ ?_
        · dsimp; simp
        · dsimp
          simp only [assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
          erw [← u.naturality_assoc, ← u.naturality]
          rfl)
    (by dsimp
        refine biprod.hom_ext _ _ ?_ ?_
        · refine biprod.hom_ext' _ _ ?_ ?_
          · dsimp
            simp only [assoc, biprod.map_fst, biprod.inl_map_assoc]
            change _ ≫ biprod.map _ _ ≫ _ = _ ≫ _ ≫ biprod.map _ _ ≫ _
            simp only [biprod.map_fst_assoc, BinaryBicone.inl_fst_assoc, biprod.map_fst]
            exact u.naturality _
          · dsimp
            simp only [assoc, biprod.map_fst, biprod.inr_map_assoc]
            change _ ≫ biprod.map _ _ ≫ _ = _ ≫ _ ≫ biprod.map _ _ ≫ _
            simp
        · refine biprod.hom_ext' _ _ ?_ ?_
          · dsimp
            simp only [assoc, biprod.map_snd, biprod.inl_map_assoc]
            change _ ≫ biprod.map _ _ ≫ _ = _ ≫ _ ≫ biprod.map _ _ ≫ _
            simp
          · dsimp
            simp only [assoc, biprod.map_snd, biprod.inr_map_assoc]
            change _ ≫ biprod.map _ _ ≫ _ = _ ≫ _ ≫ biprod.map _ _ ≫ _
            simp)
  map_id X := by
    ext
    · dsimp
    · dsimp
      rw [biprod.ext_to_iff, biprod.ext_from_iff]
      simp only [biprod.map_fst, comp_id, BinaryBicone.inl_fst, id_comp,
        BinaryBicone.inr_fst, and_self, biprod.map_snd, true_and]
      erw [comp_id]
    · dsimp
      rw [biprod.ext_to_iff, biprod.ext_from_iff]
      simp only [biprod.map_fst, BinaryBicone.inl_fst_assoc, homOfLE_leOfHom,
        BinaryBicone.inr_fst_assoc, zero_comp, biprod.map_snd]
      refine ⟨?_, ?_⟩
      · erw [id_comp]; simp; rfl
      · erw [comp_id, id_comp]
  map_comp _ _ := by
    ext
    · dsimp
    · dsimp
      rw [biprod.ext_to_iff, biprod.ext_from_iff]
      simp
    · dsimp
      rw [biprod.ext_to_iff, biprod.ext_from_iff]
      simp only [biprod.map_fst, BinaryBicone.inl_fst_assoc, assoc,
        BinaryBicone.inr_fst_assoc, zero_comp, biprod.map_snd]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp

noncomputable def homologyπ : cycles C ⟶ homology C where
  app X := ComposableArrows.homMk₂ 0 biprod.inl biprod.inl (by dsimp [cycles]; simp)
    (by change X.map' 1 2 ≫ biprod.inl = biprod.inl ≫ biprod.map (X.map' 1 2) (𝟙 (X.obj two))
        simp)
  naturality {_ _} u := by
    dsimp [cycles, homology]
    ext
    · dsimp; simp
    · dsimp; simp
    · change u.app two ≫ biprod.inl = biprod.inl ≫ biprod.map _ _
      rw [biprod.inl_map]

variable {C}

noncomputable def homology_iso_candcoker (X : ComposableArrows C 2) : (homology C).obj X ≅
    candcoker ((tocycles C).app X) := by
  refine ComposableArrows.isoMk₂ ?_ ?_ ?_ ?_ ?_
  · exact isoZeroBiprod (isZero_zero _)
  · exact Iso.refl _
  · exact Iso.refl _
  · dsimp [tocycles, homology, cycles, contract₁]
    simp only [comp_id, Preadditive.comp_add, biprod.inr_map, BinaryBicone.inr_snd_assoc]
    change  _ = (X.map' 0 1 ≫ X.map' 1 2) ≫ _ + _
    refine biprod.hom_ext _ _ ?_ ?_
    · dsimp
      simp only [biprod.lift_fst, assoc, Preadditive.add_comp]
      erw [biprod.inr_fst, biprod.inl_fst]
      simp
    · dsimp
      simp only [biprod.lift_snd, assoc, Preadditive.add_comp]
      erw [biprod.inr_snd, biprod.inl_snd]
      simp
  · dsimp [homology, tocycles, cycles, contract₁]
    simp only [comp_id, id_comp]
    rfl

lemma π_homology_iso_candker (X : ComposableArrows C 2) :
    (homologyπ C).app X ≫ (homology_iso_candcoker X).hom = candπ _ := by
  dsimp [homology_iso_candcoker, tocycles, cycles, homologyπ]
  ext
  · dsimp
    rw [biprod.ext_to_iff]
    simp
  · dsimp; simp; rfl
  · dsimp
    change biprod.inl ≫ 𝟙 _ = _
    rw [comp_id]
    rfl

noncomputable def homology_cocone (X : ComposableArrows C 2) :
    CokernelCofork ((contract C).obj X).toCycles := by
  refine Cofork.ofπ ((cycles_iso_cycles C).inv.app X ≫ (quotient C).map ((homologyπ C).app X)) ?_
  rw [zero_comp, ← assoc, to_cycles_iso_cycles_inv, ← (quotient C).map_comp,
    ← (quotient C).map_zero, quotient_map_eq_iff]
  use 𝟙 _, -biprod.inr
  dsimp [tocycles, homologyπ, contract₁, homology]
  simp only [id_comp, Preadditive.comp_neg, add_zero]
  change _ = _ + (- (X.map' 0 1 ≫ X.map' 1 2) ≫ _)
  rw [biprod.ext_to_iff]
  dsimp
  simp only [assoc, Preadditive.add_comp, biprod.lift_fst,
    Preadditive.neg_comp, BinaryBicone.inr_fst, comp_zero, neg_zero, add_zero, biprod.lift_snd,
    BinaryBicone.inr_snd, comp_id, add_neg_cancel]
  erw [biprod.inl_fst, comp_id, biprod.inl_snd, comp_zero]
  simp

noncomputable def homology_isCokernel (X : ComposableArrows C 2) :
    IsColimit (homology_cocone X) := by
  set α : parallelPair ((quotient C).map ((tocycles C).app X)) 0 ≅
      parallelPair ((contract C).obj X).toCycles 0 := by
    refine NatIso.ofComponents (fun j ↦ ?_) (fun u ↦ ?_)
    · match j with
      | .zero => exact Iso.refl _
      | .one => exact (cycles_iso_cycles C).app X
    · match u with
      | .id _ => dsimp; simp
      | .left => dsimp; rw [to_cycles_iso_cycles_hom, id_comp]
      | .right => dsimp; simp
  refine (IsColimit.precomposeHomEquiv α _ ).toFun ?_
  refine (cocone_isColimit _).ofIsoColimit ?_
  refine Cofork.ext ((quotient C).mapIso (homology_iso_candcoker X)).symm ?_
  rw [← cancel_mono ((quotient C).mapIso (homology_iso_candcoker X)).symm.inv,
    assoc, Iso.hom_inv_id, comp_id]
  change _ = (Cocone.ι _).app WalkingParallelPair.one ≫ _
  dsimp [α, homology_cocone]
  rw [Iso.hom_inv_id_app_assoc, ← (quotient C).map_comp, π_homology_iso_candker]
  rfl

variable (C) in
noncomputable def homology_iso_homology :
    contract C ⋙ ShortComplex.homologyFunctor (Adel C) ≅ homology C ⋙ quotient C := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun {X Y} u ↦ ?_)
  · exact ((contract C).obj X).homologyIsCokernel.coconePointUniqueUpToIso (homology_isCokernel X)
  · dsimp
    rw [← cancel_epi ((contract C).obj X).homologyπ, ← assoc, ShortComplex.homologyπ_naturality,
      assoc]
    erw [((contract C).obj Y).homologyIsCokernel.comp_coconePointUniqueUpToIso_hom
      (homology_isCokernel Y) WalkingParallelPair.one,
      ((contract C).obj X).homologyIsCokernel.comp_coconePointUniqueUpToIso_hom_assoc
      (homology_isCokernel X) WalkingParallelPair.one]
    dsimp [homology_cocone]
    have eq : ShortComplex.cyclesMap ((contract C).map u) ≫ (cycles_iso_cycles C).inv.app Y =
        (cycles_iso_cycles C).inv.app X ≫ (quotient C).map ((cycles C).map u) := by
      rw [← cancel_mono ((cycles_iso_cycles C).hom.app Y), assoc, Iso.inv_hom_id_app,
      ← cancel_mono ((contract C).obj Y).iCycles, assoc, assoc, cycles_iso_cycles_i, assoc,
      ← (quotient C).map_comp, (icycles C).naturality, ← assoc]
      erw [comp_id]
      rw [ShortComplex.cyclesMap_i, ← cancel_epi ((cycles_iso_cycles C).hom.app X),
        Iso.hom_inv_id_app_assoc, ← assoc, cycles_iso_cycles_i]
      rfl
    rw [← assoc, eq, assoc, assoc, cancel_epi ((cycles_iso_cycles C).inv.app X),
      ← (quotient C).map_comp, ← (quotient C).map_comp]
    congr 1
    exact (homologyπ C).naturality _

lemma π_homology_iso_homology (X : ComposableArrows C 2) :
    ((contract C).obj X).homologyπ ≫ (homology_iso_homology C).hom.app X  =
    (cycles_iso_cycles C).inv.app X ≫ (quotient C).map ((homologyπ C).app X) := by
  dsimp [homology_iso_homology]
  erw [((contract C).obj X).homologyIsCokernel.comp_coconePointUniqueUpToIso_hom
    (homology_isCokernel X) WalkingParallelPair.one]
  rfl

variable (C) in
noncomputable def homology_iso_id : homology C ⋙ quotient C ≅ quotient C := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun u ↦ ?_)
  · refine {hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_}
    · exact (quotient C).map (ComposableArrows.homMk₂ (𝟙 _) biprod.fst biprod.fst
        (by dsimp [homology]; simp) (by change biprod.map _ _ ≫ _ = _; simp))
    · exact (quotient C).map (ComposableArrows.homMk₂ (𝟙 _) (biprod.lift (𝟙 _) (X.map' 1 2))
        (biprod.lift (𝟙 _) (𝟙 _)) (by dsimp [homology]; rw [biprod.ext_to_iff]; simp)
        (by change _ = _ ≫ biprod.map _ _; rw [biprod.ext_to_iff]; simp))
    · dsimp
      rw [← (quotient C).map_comp, ← (quotient C).map_id, quotient_map_eq_iff]
      use 0, (biprod.fst - biprod.snd) ≫ biprod.inr
      dsimp [homology]
      change _ = _ + biprod.map _ _ ≫ _ + _
      rw [biprod.ext_from_iff, biprod.ext_to_iff, biprod.ext_to_iff]
      simp
    · rw [← (quotient C).map_comp, ← (quotient C).map_id]
      congr 1
      ext
      · dsimp; simp
      · dsimp; simp
      · change biprod.lift _ _ ≫ biprod.fst = _; simp
  · dsimp [homology]
    rw [← (quotient C).map_comp, ← (quotient C).map_comp]
    congr 1
    ext
    · dsimp; simp
    · dsimp; simp
    · change biprod.map _ _ ≫ biprod.fst = biprod.fst ≫ _; simp; rfl

end Calculs

end Functor

end CategoryTheory
