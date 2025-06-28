import Mathlib.CategoryTheory.Preadditive.LeftExact
import Nori.Mathlib.CategoryTheory.Quotient.Preadditive
import Nori.Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Nori.Homology

universe u v u' v'

open CategoryTheory Category Functor Limits Adel

open scoped ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive]

instance : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F

namespace CategoryTheory

namespace Functor

lemma functorAdel_aux (X Y : ComposableArrows C 2) (f g : X ⟶ Y) (h : homotopic f g) :
    (F.mapComposableArrows 2 ⋙ Adel.quotient D).map f =
    (F.mapComposableArrows 2 ⋙ Adel.quotient D).map g := by
  obtain ⟨σ₁, σ₂, eq⟩ := h
  dsimp
  rw [quotient_map_eq_iff]
  use F.map σ₁, F.map σ₂
  dsimp at eq ⊢
  rw [eq]
  simp

def functorAdel : Adel C ⥤ Adel D := by
  refine Quotient.lift _ (F.mapComposableArrows 2 ⋙ Adel.quotient D) (functorAdel_aux F)

section Compat

variable [HasZeroObject C] [HasZeroObject D]

noncomputable def functor_mapComposableArrows : functor_aux C ⋙ F.mapComposableArrows 2 ≅
    F ⋙ functor_aux D := by
  refine NatIso.ofComponents (fun X ↦ ?_) (fun f ↦ ?_)
  · refine ComposableArrows.isoMk₂ F.mapZeroObject (Iso.refl _) F.mapZeroObject ?_ ?_
    · dsimp [functor_aux, functor_aux_complex]; simp
    · dsimp [functor_aux, functor_aux_complex]; change _ = _ ≫ 0; simp
  · ext
    · dsimp; simp
    · dsimp [functor_aux, functor_aux_complex]; simp
    · dsimp; change _ ≫ 0 = 0 ≫ _; simp

noncomputable def functor_functorAdel : functor C ⋙ F.functorAdel ≅ F ⋙ functor D :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (functor_aux C) (Quotient.lift.isLift _
  (F.mapComposableArrows 2 ⋙ Adel.quotient D) (functorAdel_aux F)) ≪≫
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight F.functor_mapComposableArrows (quotient D)

end Compat

section Compat

variable [HasFiniteBiproducts C]

local instance : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts _

section Calculs

open CandidateKer CandidateCoker

variable (C)

noncomputable def contract₁ :
    ComposableArrows C 2 ⥤ ComposableArrows C 2 where
  obj X := ComposableArrows.mk₂ (0 : 0 ⟶ X.obj zero) (X.map' 0 1 ≫ X.map' 1 2)
  map u := ComposableArrows.homMk₂ 0 (u.app zero) (u.app two)
    (by dsimp; simp) (by change (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
                         rw [assoc, u.naturality, u.naturality_assoc])
  map_id X := by
    ext
    · dsimp; simp
    · dsimp
    · dsimp; rfl
  map_comp _ _ := by
    ext
    · dsimp; simp
    · dsimp
    · dsimp; rfl

/-
noncomputable def contract₀  : ComposableArrows C 2 ⥤ ComposableArrows C 2 :=
  (evaluation _ _).obj zero ⋙ functor_aux C

noncomputable def contract_ι : contract₁ C ⟶ contract₀ C where
  app X := ComposableArrows.homMk₂ 0 (𝟙 _) 0 (by change 0 ≫ _ = _ ≫ 0; simp)
    (by change _ ≫ 0 = _ ≫ 0; simp)
  naturality _ _ u := by
    ext
    · dsimp; simp
    · dsimp; simp; rfl
    · change _ ≫ 0 = 0 ≫ _; simp
-/


variable {C}

noncomputable def contract₁_iso_candker (X : ComposableArrows C 2) : (contract₁ C).obj X ≅
    candker ((functor_aux C).map (X.map' 0 1) ≫ (functor_aux C).map (X.map' 1 2)) := by
  refine ComposableArrows.isoMk₂ ?_ ?_ ?_ ?_ ?_
  · exact isoBiprodZero (isZero_zero _)
  · exact isoBiprodZero (isZero_zero _)
  · exact isoZeroBiprod (isZero_zero _)
  · dsimp [contract₁, functor_aux, functor_aux_complex]
    simp
  · simp only [NatTrans.comp_app, id_eq, isoZeroBiprod_hom, isoBiprodZero_hom]
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
  ext
  · dsimp [contract₁_iso_candker, contract₁, contract₁_ι]
    erw [biprod.inl_fst]
    simp
  · dsimp [contract₁_iso_candker, contract₁_ι]
    erw [biprod.inl_fst]
  · dsimp [contract₁_iso_candker, contract₁_ι]
    change biprod.inr ≫ biprod.fst  = _
    rw [biprod.inr_fst]



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
  refine NatIso.ofComponents (fun X ↦ ?_) (fun u ↦ ?_)
  · sorry
  · sorry

/-variable (X : ComposableArrows C 2)

noncomputable abbrev complex₁ : ComposableArrows C 2 :=
  ComposableArrows.mk₂ (0 : 0 ⟶ X.obj zero) (X.map' 0 1 ≫ X.map' 1 2)

noncomputable abbrev complex₁_kernel : complex₁ X ≅
    candker ((functor_aux C).map (X.map' 0 1) ≫ (functor_aux C).map (X.map' 1 2)) := by
  refine ComposableArrows.isoMk₂ ?_ ?_ ?_ ?_ ?_
  · change 0 ≅ biprod 0 0
    exact isoBiprodZero (isZero_zero _)
  · change X.obj zero ≅ biprod (X.obj 0) 0
    exact isoBiprodZero (isZero_zero _)
  · change _ ≅ biprod 0 _
    exact isoZeroBiprod (isZero_zero _)
  · dsimp [functor_aux, functor_aux_complex]
    simp
  · simp only [NatTrans.comp_app, id_eq, isoZeroBiprod_hom, isoBiprodZero_hom]
    change _ = _ ≫ (biprod.map _ _  + _)
    rw [Preadditive.comp_add, biprod.inl_map]
    erw [biprod.inl_fst_assoc]
    change _ = 0 ≫ _ + _ ≫ _
    rw [zero_comp, zero_add]
    rfl

lemma complex₁_candι : (complex₁_kernel X).hom ≫ candι _ ≫ (functor_aux C).map (X.map' 0 1) =
    ComposableArrows.homMk₂ 0 (X.map' 0 1) 0 (by simp) (by change _ = _ ≫ 0; simp) := by
  ext
  · change _ ≫ _ ≫ 0 = 0
    simp
  · change biprod.inl ≫ biprod.fst ≫ _ = _
    rw [biprod.inl_fst_assoc]
    rfl
  · change biprod.inr ≫ biprod.fst ≫ _ = 0
    rw [biprod.inr_fst_assoc, zero_comp]

lemma complex₁_condition : homotopic (((complex₁_kernel X).hom ≫ candι _ ≫
    (functor_aux C).map (X.map' 0 1)) ≫ (functor_aux C).map (X.map' 1 2)) 0 := by
  use 0, 𝟙 (X.obj two)
  change _ = 0 ≫ 0 + _ ≫ _ + _
  rw [zero_comp, zero_add, NatTrans.app_zero, add_zero]
  erw [comp_id]
  dsimp
  erw [biprod.inl_fst_assoc]
  rfl

noncomputable abbrev complex₂ : ComposableArrows C 2 :=
  ComposableArrows.mk₂ (0 : 0 ⟶ X.obj one) (X.map' 1 2)

noncomputable abbrev complex₂_kernel : complex₂ X ≅
    candker ((functor_aux C).map (X.map' 1 2)) := by
  refine ComposableArrows.isoMk₂ ?_ ?_ ?_ ?_ ?_
  · change 0 ≅ biprod 0 0
    exact isoBiprodZero (isZero_zero _)
  · change X.obj one ≅ biprod (X.obj one) 0
    exact isoBiprodZero (isZero_zero _)
  · change _ ≅ biprod 0 _
    exact isoZeroBiprod (isZero_zero _)
  · dsimp [functor_aux, functor_aux_complex]
    simp
  · simp only [NatTrans.comp_app, id_eq, isoZeroBiprod_hom, isoBiprodZero_hom]
    change _ = _ ≫ (biprod.map _ _  + _)
    rw [Preadditive.comp_add, biprod.inl_map]
    erw [biprod.inl_fst_assoc]
    change _ = 0 ≫ _ + _ ≫ _
    rw [zero_comp, zero_add]
    rfl

noncomputable abbrev complex₁ToComplex₂ : complex₁ X ⟶ complex₂ X := by
  refine ComposableArrows.homMk₂ 0 (X.map' 0 1) (𝟙 _) ?_ ?_
  · dsimp; simp
  · change (X.map' 0 1 ≫ X.map' 1 2) ≫ _ = _
    erw [comp_id]
    rfl

lemma complex₁ToComplex₂_condition : complex₁ToComplex₂ X ≫ (complex₂_kernel X).hom
    ≫ candι _ = (complex₁_kernel X).hom ≫ candι _ ≫ (functor_aux C).map (X.map' 0 1) := by
  rw [complex₁_candι X]
  ext
  · dsimp; simp
  · dsimp; erw [biprod.inl_fst]; rw [comp_id]
  · dsimp
    change (𝟙 _) ≫ biprod.inr ≫ biprod.fst = 0
    rw [biprod.inr_fst, comp_zero]

noncomputable abbrev complex₃ : ComposableArrows C 2 :=
  ComposableArrows.mk₂ (biprod.lift (X.map' 0 1) (X.map' 0 1 ≫ X.map' 1 2))
  (biprod.map (X.map' 1 2) (𝟙 (X.obj two)))

noncomputable abbrev complex₃_cokernel : complex₃ X ≅ candcoker (complex₁ToComplex₂ X) := by
  refine ComposableArrows.isoMk₂ ?_ (Iso.refl _) (Iso.refl _) ?_ ?_
  · change _ ≅ biprod 0 _
    exact isoZeroBiprod (isZero_zero _)
  · dsimp
    rw [Preadditive.comp_add, biprod.inr_map, comp_id, biprod.inr_snd_assoc]
    refine biprod.hom_ext _ _ ?_ ?_
    · dsimp
      simp only [biprod.lift_fst, Preadditive.add_comp, assoc]
      erw [biprod.inr_fst, biprod.inl_fst]
      rw [comp_zero, comp_id, zero_add]
    · dsimp
      simp only [biprod.lift_snd, Preadditive.add_comp, assoc]
      erw [biprod.inr_snd, biprod.inl_snd]
      rw [comp_zero, add_zero, comp_id]
      rfl
  · dsimp
    rw [comp_id, id_comp]
    rfl
-/


/-noncomputable abbrev complex₁_out : complex₁ X ⟶ (functor C).obj (X.obj one) :=
  (quotient C).map (ComposableArrows.homMk₂ 0 (X.map' 0 1) 0 (by simp)
  (by change _ = _ ≫ 0; simp))

lemma complex₁_out_zero : complex₁_out X ≫ (functor C).map (X.map' 1 2) = 0 := by
  dsimp [functor, complex₁_out]
  rw [← (quotient C).map_comp, ← (quotient C).map_zero]
  rw [quotient_map_eq_iff]
  use 0, 𝟙 (X.obj two)
  change _ = 0 ≫ 0 + _ ≫ _ + _
  dsimp [functor_aux]
  simp only [comp_zero, zero_add, add_zero]
  erw [comp_id]
  rfl

noncomputable abbrev truc₁_X₁ (X : ComposableArrows C 2) : ((contractLeft (Adel C)).obj
    (((functor C).mapComposableArrows 2).obj X)).X₁ ≅ complex₁ X := by
  dsimp [contractLeft]
  sorry

noncomputable def truc₁ (X : ComposableArrows C 2) : (contractLeft (Adel C)).obj
    (((functor C).mapComposableArrows 2).obj X) ≅
    ShortComplex.mk (complex₁_out X) ((functor C).map (X.map' 1 2)) (complex₁_out_zero X) := by
  refine ShortComplex.isoMk ?_ ?_ ?_ ?_ ?_
  · refine IsZero.iso ?_ ?_
    · dsimp [contractLeft]
    · sorry
-/

end Calculs

noncomputable def truc : (functor C).functorAdel ⋙ homologyLeftAbelian (Adel C) ≅ 𝟭 (Adel C) := by
  refine Quotient.natIsoLift _ ?_
  refine ?_ ≪≫ (Quotient.functor Adel.homotopic).rightUnitor.symm
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  refine isoWhiskerRight (Quotient.lift.isLift _ ((functor C).mapComposableArrows 2 ⋙
    Adel.quotient _) (functorAdel_aux (functor C))) _ ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft ((functor C).mapComposableArrows 2) (Quotient.lift.isLift _ _ _) ≪≫ ?_
  dsimp [homologyLeft]
  sorry

end Compat

instance (n : ℕ) : (F.mapComposableArrows n).Additive where
  map_add {X Y f g} := by
    ext
    dsimp; simp

instance : F.functorAdel.Additive :=
  Quotient.lift_additive (homotopic (C := C)) _ (F.mapComposableArrows 2 ⋙ Adel.quotient D) _

section PreservesCokernels

variable [HasBinaryBiproducts C] [HasBinaryBiproducts D] {X Y : ComposableArrows C 2} (u : X ⟶ Y)

open CandidateCoker

@[simp]
noncomputable def candcoker_map_iso : candcoker ((F.mapComposableArrows 2).map u) ≅
    (F.mapComposableArrows 2).obj (candcoker u) := by
  refine ComposableArrows.isoMk₂ (F.mapBiprod _ _).symm (F.mapBiprod _ _).symm
    (F.mapBiprod _ _).symm ?_ ?_
  · refine biprod.hom_ext' _ _ ?_ ?_
    · dsimp
      rw [Preadditive.add_comp, Preadditive.comp_add, biprod.inl_map_assoc, biprod.inl_desc,
              biprod.inl_desc_assoc, ← F.map_comp biprod.inl, Preadditive.comp_add, biprod.inl_map,
              biprod.inl_snd_assoc, zero_comp, add_zero]
      simp
      rfl
    · dsimp
      rw [Preadditive.add_comp, Preadditive.comp_add, biprod.inr_map_assoc, biprod.inr_desc,
              biprod.inr_desc_assoc, ← F.map_comp biprod.inr, Preadditive.comp_add, biprod.inr_map,
              biprod.inr_snd_assoc]
      simp
      rfl
  · refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [mapComposableArrows_obj_obj, mapComposableArrows_obj_map,
            mapComposableArrows_map_app, Iso.symm_hom,
            biprod.uniqueUpToIso_inv, mapBinaryBicone_pt, mapBinaryBicone_inl,
            BinaryBiproduct.bicone_inl, mapBinaryBicone_inr, BinaryBiproduct.bicone_inr,
            biprod.inl_desc_assoc]
      change biprod.inl ≫ biprod.map _ _ ≫ _ = _
      rw [biprod.inl_map_assoc, biprod.inl_desc, ← F.map_comp biprod.inl]
      change _ = F.map (_ ≫ biprod.map _ _)
      rw [biprod.inl_map]
      simp
    · simp only [mapComposableArrows_obj_obj, mapComposableArrows_obj_map,
            mapComposableArrows_map_app, Iso.symm_hom,
            biprod.uniqueUpToIso_inv, mapBinaryBicone_pt, mapBinaryBicone_inl,
            BinaryBiproduct.bicone_inl, mapBinaryBicone_inr, BinaryBiproduct.bicone_inr,
            biprod.inr_desc_assoc]
      change biprod.inr ≫ biprod.map _ _ ≫ _ = _
      rw [biprod.inr_map_assoc, biprod.inr_desc, ← F.map_comp biprod.inr]
      change _ = F.map (_ ≫ biprod.map _ _)
      rw [biprod.inr_map]
      simp

noncomputable def preservesCokernelsComposableArrows_aux :
    IsColimit (F.functorAdel.mapCocone (cocone_aux u)) := by
  set α : parallelPair ((quotient C).map u) 0 ⋙ F.functorAdel ≅
      parallelPair ((quotient D).map ((F.mapComposableArrows 2).map u)) 0 := by
    refine NatIso.ofComponents (fun j ↦ ?_) (fun u ↦ ?_)
    · match j with
      | .zero => exact Iso.refl _
      | .one => exact Iso.refl _
    · match u with
      | .id _ => dsimp; simp
      | .left =>
        dsimp [functorAdel, quotient]
        simp only [comp_id, id_comp]
        rfl
      | .right => dsimp; simp
  set e : (Cocones.precompose α.hom).obj (cocone_aux ((F.mapComposableArrows 2).map u)) ≅
      (F.functorAdel.mapCocone (cocone_aux u)) := by
    refine Cocones.ext ?_ (fun j ↦ ?_)
    · dsimp
      change (quotient D).obj _ ≅ F.functorAdel.obj ((quotient C).obj _)
      refine (quotient D).mapIso (candcoker_map_iso F u) ≪≫ ?_
      rw [← Functor.comp_obj, ← Functor.comp_obj]
      exact (Quotient.lift.isLift _ _ _).symm.app (candcoker u)
    · match j with
      | .zero =>
        dsimp [α]
        simp only [id_comp, comp_id, map_comp]
        have h₁ := (cocone_aux u).w WalkingParallelPairHom.right
        simp only [comp_obj, parallelPair_obj_zero, const_obj_obj, parallelPair_obj_one,
          comp_map, parallelPair_map_right, Functor.map_zero, zero_comp] at h₁
        have h₂ := (cocone_aux ((F.mapComposableArrows 2).map u)).w WalkingParallelPairHom.right
        simp only [comp_obj, parallelPair_obj_zero, const_obj_obj, parallelPair_obj_one,
          comp_map, parallelPair_map_right, Functor.map_zero, zero_comp] at h₂
        rw [← h₁, ← h₂]
        simp
      | .one =>
        dsimp [α, compNatIso', cocone_aux, candπ, functorAdel]
        simp only [comp_id, map_comp, Functor.map_id, id_comp]
        rw [← (quotient D).map_comp]
        change _ = (quotient D).map _
        congr 1
        ext
        · dsimp; simp
        · dsimp; simp
        · simp only [mapComposableArrows_obj_obj, NatTrans.comp_app, mapComposableArrows_map_app,
            ComposableArrows.homMk₂_app_two, biprod.inl_desc]
  exact IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α _).invFun (cocone_isColimit _)) e

def preservesCokernelsComposableArrows : PreservesColimit (parallelPair ((quotient C).map u) 0)
    F.functorAdel where
  preserves hc :=
    Nonempty.intro ((preservesCokernelsComposableArrows_aux F u).ofIsoColimit
    ((Cocones.functoriality _ F.functorAdel).mapIso (hc.uniqueUpToIso (cocone_isColimit u))).symm)

instance {X Y : Adel C} (u : X ⟶ Y) : PreservesColimit (parallelPair u 0) F.functorAdel :=
  preservesCokernels_of_preservesCokernelsComposableArrows F.functorAdel
  F.preservesCokernelsComposableArrows u

end PreservesCokernels

section PreservesKernels

variable [HasBinaryBiproducts C] [HasBinaryBiproducts D] {X Y : ComposableArrows C 2} (u : X ⟶ Y)

open CandidateKer

@[simp]
noncomputable def candker_map_iso : candker ((F.mapComposableArrows 2).map u) ≅
    (F.mapComposableArrows 2).obj (candker u) := by
  refine ComposableArrows.isoMk₂ (F.mapBiprod _ _).symm (F.mapBiprod _ _).symm
    (F.mapBiprod _ _).symm ?_ ?_
  · refine biprod.hom_ext' _ _ ?_ ?_
    · dsimp
      simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      rw [← F.map_comp biprod.inl, biprod.inl_map, F.map_comp]
    · dsimp
      simp only [biprod.inr_map_assoc, biprod.inr_desc, id_comp, biprod.inr_desc_assoc]
      rw [← F.map_comp, biprod.inr_map, id_comp]
  · refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [mapComposableArrows_obj_obj, mapComposableArrows_obj_map,
        mapComposableArrows_map_app, Iso.symm_hom, biprod.uniqueUpToIso_inv, mapBinaryBicone_pt,
        mapBinaryBicone_inl, BinaryBiproduct.bicone_inl, mapBinaryBicone_inr,
        BinaryBiproduct.bicone_inr, biprod.inl_desc_assoc]
      change biprod.inl ≫ (biprod.map _ _  + _) ≫ _ = _ ≫ F.map (biprod.map _ _ + _)
      simp only [mapComposableArrows_obj_obj, mapComposableArrows_obj_map,
        mapComposableArrows_map_app, Preadditive.add_comp, assoc, biprod.inr_desc,
        Preadditive.comp_add, biprod.inl_map_assoc, biprod.inl_desc,
        BinaryBicone.inl_fst_assoc, map_add, map_comp]
      rw [← F.map_comp biprod.inl, biprod.inl_map, ← F.map_comp (u.app one),
        ← F.map_comp biprod.fst, ← F.map_comp biprod.inl, biprod.inl_fst_assoc,
        F.map_comp (X.map' 1 2)]
    · change biprod.inr ≫ (biprod.map _ _ + _) ≫ _ = _
      simp only [mapComposableArrows_obj_obj, mapComposableArrows_obj_map,
        mapComposableArrows_map_app, Iso.symm_hom, biprod.uniqueUpToIso_inv, mapBinaryBicone_pt,
        mapBinaryBicone_inl, BinaryBiproduct.bicone_inl, mapBinaryBicone_inr,
        BinaryBiproduct.bicone_inr, Preadditive.add_comp, assoc, biprod.inr_desc,
        Preadditive.comp_add, biprod.inr_map_assoc, BinaryBicone.inr_fst_assoc, zero_comp, add_zero,
        biprod.inr_desc_assoc]
      change _ = _ ≫ F.map (biprod.map _ _ + _)
      rw [← F.map_comp biprod.inr, Preadditive.comp_add, biprod.inr_map]
      simp

noncomputable def preservesKernelsComposableArrows_aux :
    IsLimit (F.functorAdel.mapCone (cone_aux u)) := by
  set α : parallelPair ((quotient C).map u) 0 ⋙ F.functorAdel ≅
      parallelPair ((quotient D).map ((F.mapComposableArrows 2).map u)) 0 := by
    refine NatIso.ofComponents (fun j ↦ ?_) (fun u ↦ ?_)
    · match j with
      | .zero => exact Iso.refl _
      | .one => exact Iso.refl _
    · match u with
      | .id _ => dsimp; simp
      | .left =>
        dsimp [functorAdel, quotient]
        simp only [comp_id, id_comp]
        rfl
      | .right => dsimp; simp
  set e : (Cones.postcompose α.inv).obj (cone_aux ((F.mapComposableArrows 2).map u)) ≅
      (F.functorAdel.mapCone (cone_aux u)) := by
    refine Cones.ext ?_ (fun j ↦ ?_)
    · dsimp
      change (quotient D).obj _ ≅ F.functorAdel.obj ((quotient C).obj _)
      refine (quotient D).mapIso (candker_map_iso F u) ≪≫ ?_
      rw [← Functor.comp_obj, ← Functor.comp_obj]
      exact (Quotient.lift.isLift _ _ _).symm.app (candker u)
    · match j with
      | .zero =>
        dsimp [α, compNatIso', cocone_aux, candι, functorAdel]
        simp only [comp_id]
        change (quotient D).map _ = _
        congr 1
        ext
        · rw [← cancel_epi (F.mapBiprod _ _).hom]
          dsimp
          simp only [biprod.lift_fst_assoc, biprod.lift_desc_assoc, Preadditive.add_comp, assoc]
          rw [← F.map_comp, ← F.map_comp, biprod.inl_fst, ← F.map_comp, ← F.map_comp]
          erw [biprod.inr_fst, comp_id, comp_id]
          simp
        · rw [← cancel_epi (F.mapBiprod _ _).hom]
          dsimp
          simp only [biprod.lift_fst_assoc, biprod.lift_desc_assoc, Preadditive.add_comp, assoc]
          rw [← F.map_comp, ← F.map_comp, biprod.inl_fst, ← F.map_comp, ← F.map_comp]
          erw [comp_id, comp_id, biprod.inr_fst]
          simp
        · rw [← cancel_epi (F.mapBiprod _ _).hom]
          dsimp [candι]
          erw [comp_id, ComposableArrows.homMk₂_app_two, ComposableArrows.homMk₂_app_two,
            ComposableArrows.homMk₂_app_two, biprod.lift_fst]
          rw [biprod.lift_desc_assoc, ← F.map_comp, ← F.map_comp, Preadditive.add_comp,
            ← F.map_comp, ← F.map_comp, assoc, assoc, biprod.inl_fst, comp_id]
          erw [biprod.inr_fst]
          simp
      | .one =>
        dsimp [α]
        simp only [comp_id, map_comp]
        have h₁ := (cone_aux ((F.mapComposableArrows 2).map u)).w WalkingParallelPairHom.right
        have h₂ := (cone_aux u).w WalkingParallelPairHom.right
        simp only [const_obj_obj, comp_obj, parallelPair_obj_one, parallelPair_obj_zero,
          comp_map, parallelPair_map_right, Functor.map_zero, comp_zero] at h₁ h₂
        rw [← h₁, ← h₂]
        simp
  exact IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α.symm _).invFun (cone_isLimit _)) e

def preservesKernelsComposableArrows : PreservesLimit (parallelPair ((quotient C).map u) 0)
    F.functorAdel where
  preserves hc :=
    Nonempty.intro ((preservesKernelsComposableArrows_aux F u).ofIsoLimit ((Cones.functoriality _
    F.functorAdel).mapIso (hc.uniqueUpToIso (cone_isLimit u))).symm)

instance {X Y : CategoryTheory.Adel C} (u : X ⟶ Y) : PreservesLimit (parallelPair u 0) F.functorAdel :=
  preservesKernels_of_preservesKernelsComposableArrows F.functorAdel
  F.preservesKernelsComposableArrows u

end PreservesKernels

section PreservesFiniteLimits

variable [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [F.Additive]

local instance : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C

instance : PreservesFiniteColimits F.functorAdel :=
  F.functorAdel.preservesFiniteColimits_of_preservesCokernels

instance : PreservesFiniteLimits F.functorAdel :=
  F.functorAdel.preservesFiniteLimits_of_preservesKernels

end PreservesFiniteLimits

end Functor

end CategoryTheory
