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
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · dsimp [functor_aux]
    sorry
  · sorry

noncomputable def functor_functorAdel : functor C ⋙ F.functorAdel ≅ F ⋙ functor D :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (functor_aux C) (Quotient.lift.isLift _
  (F.mapComposableArrows 2 ⋙ Adel.quotient D) (functorAdel_aux F)) ≪≫
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight F.functor_mapComposableArrows (quotient D)

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
    IsColimit (F.functorAdel.mapCocone ((Cocones.precompose
    (compNatIso' (quotient C)).inv).obj (cocone_aux u))) := by
  set α : parallelPair ((quotient C).map u) 0 ⋙ F.functorAdel ≅
      parallelPair ((F.mapComposableArrows 2).map u) 0 ⋙ quotient D := by
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
      (F.functorAdel.mapCocone ((Cocones.precompose (compNatIso' (quotient C)).inv).obj
      (cocone_aux u))) := by
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
  preserves {c} hc := by
    set e := hc.uniqueUpToIso ((IsColimit.precomposeHomEquiv (compNatIso' (quotient C)).symm
      (cocone_aux u)).invFun (cocone_isColimit u))
    have h : IsColimit (F.functorAdel.mapCocone ((Cocones.precompose (compNatIso'
      (quotient C)).inv).obj (cocone_aux u))) := preservesCokernelsComposableArrows_aux F u
    exact Nonempty.intro (h.ofIsoColimit ((Cocones.functoriality _ F.functorAdel).mapIso e).symm)

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
    IsLimit (F.functorAdel.mapCone ((Cones.postcompose
    (compNatIso' (quotient C)).hom).obj (cone_aux u))) := by
  set α : parallelPair ((quotient C).map u) 0 ⋙ F.functorAdel ≅
      parallelPair ((F.mapComposableArrows 2).map u) 0 ⋙ quotient D := by
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
      (F.functorAdel.mapCone ((Cones.postcompose (compNatIso' (quotient C)).hom).obj
      (cone_aux u))) := by
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
        · dsimp
          simp only [comp_id]
          erw [comp_id]
          rw [← cancel_epi (F.mapBiprod _ _).hom]
          simp only [biprod.uniqueUpToIso_hom, mapBinaryBicone_pt, mapBinaryBicone_fst,
            BinaryBiproduct.bicone_fst, mapBinaryBicone_snd, BinaryBiproduct.bicone_snd,
            biprod.lift_fst, biprod.lift_desc_assoc, Preadditive.add_comp, assoc]
          rw [← F.map_comp, ← F.map_comp, biprod.inl_fst, comp_id, ← F.map_comp, ← F.map_comp]
          erw [biprod.inr_fst]
          simp
        · dsimp
          simp only [comp_id]
          rw [← cancel_epi (F.mapBiprod _ _).hom]
          simp only [biprod.uniqueUpToIso_hom,
            mapBinaryBicone_pt, mapBinaryBicone_fst, BinaryBiproduct.bicone_fst,
            mapBinaryBicone_snd, BinaryBiproduct.bicone_snd, biprod.lift_fst_assoc,
            biprod.lift_desc_assoc, Preadditive.add_comp, assoc]
          rw [← F.map_comp, ← F.map_comp, biprod.inl_fst, ← F.map_comp, ← F.map_comp]
          erw [biprod.lift_fst_assoc, biprod.inr_fst, comp_id]
          simp
        · dsimp
          simp only [comp_id]
          erw [comp_id, ComposableArrows.homMk₂_app_two, ComposableArrows.homMk₂_app_two]
          rw [← cancel_epi (F.mapBiprod _ _).hom]
          simp only [mapComposableArrows_obj_obj, biprod.uniqueUpToIso_hom, mapBinaryBicone_pt,
            mapBinaryBicone_fst, BinaryBiproduct.bicone_fst, mapBinaryBicone_snd,
            BinaryBiproduct.bicone_snd, biprod.lift_fst, biprod.lift_desc_assoc,
            Preadditive.add_comp, assoc]
          rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
          erw [biprod.inl_fst, biprod.inr_fst]
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
  preserves {c} hc := by
    set e := hc.uniqueUpToIso ((IsLimit.postcomposeHomEquiv (compNatIso' (quotient C))
      (cone_aux u)).invFun (cone_isLimit u))
    have h : IsLimit (F.functorAdel.mapCone ((Cones.postcompose (compNatIso'
      (quotient C)).hom).obj (cone_aux u))) := preservesKernelsComposableArrows_aux F u
    exact Nonempty.intro (h.ofIsoLimit ((Cones.functoriality _ F.functorAdel).mapIso e).symm)

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
