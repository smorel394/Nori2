import Nori.Mathlib.CategoryTheory.Quotient
import Nori.Functoriality
import Nori.HomologyExact
import Nori.Calculs

universe u v u' v'

open CategoryTheory Category Functor Limits Adel

open scoped ZeroObject

attribute [local instance] Functor.additive_of_preserves_binary_products

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

variable {A : Type u'} [Category.{v'} A] [Abelian A]

namespace CategoryTheory

namespace Functor

noncomputable def liftAdel (F : C ⥤ A) [F.Additive] : Adel C ⥤ A :=
  F.functorAdel ⋙ homologyLeftAbelian A

variable (F : C ⥤ A) [F.Additive]

instance : F.liftAdel.Additive := by
  dsimp [Functor.liftAdel]
  infer_instance

local instance : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

instance : PreservesFiniteLimits F.liftAdel :=
  comp_preservesFiniteLimits _ _

instance : PreservesFiniteColimits F.liftAdel :=
  comp_preservesFiniteColimits _ _

noncomputable def liftAdelIsLift : functor C ⋙ F.liftAdel ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight F.functor_functorAdel (homologyLeftAbelian A)
  ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft F (functor_homologyLeftAbelian A) ≪≫ F.rightUnitor

end Functor

section Naturality

variable {F F' : C ⥤ A} [F.Additive] [F'.Additive] (α : F ⟶ F')

lemma liftAdelIsLift_naturality : whiskerLeft (functor C)
    (whiskerRight (NatTrans.functorAdel α) (homologyLeftAbelian A)) ≫ F'.liftAdelIsLift.hom =
    F.liftAdelIsLift.hom ≫ α := by
  dsimp [Functor.liftAdelIsLift]
  simp only [assoc]
  have : whiskerLeft F (functor_homologyLeftAbelian A).hom ≫ F.rightUnitor.hom ≫ α =
      whiskerRight α (functor A ⋙ homologyLeftAbelian A) ≫ whiskerLeft F'
      (functor_homologyLeftAbelian A).hom ≫ F'.rightUnitor.hom := by
    ext
    dsimp
    simp only [id_comp, comp_id]
    rw [← Functor.comp_map, (functor_homologyLeftAbelian A).hom.naturality, Functor.id_map]
  rw [this]
  have :  (F.associator (functor A) (homologyLeftAbelian A)).hom ≫
        whiskerRight α (functor A ⋙ homologyLeftAbelian A) = whiskerRight (whiskerRight α (functor A))
        (homologyLeftAbelian A) ≫ (Functor.associator _ _ _).hom := by simp
  slice_rhs 3 4 => rw [this]
  have : whiskerRight F.functor_functorAdel.hom (homologyLeftAbelian A) ≫
      whiskerRight (whiskerRight α (functor A)) (homologyLeftAbelian A) = whiskerRight
      (whiskerLeft (functor C) (NatTrans.functorAdel α)) (homologyLeftAbelian A) ≫ whiskerRight
      F'.functor_functorAdel.hom (homologyLeftAbelian A) := by
    rw [← whiskerRight_comp, ← whiskerRight_comp]
    congr 1
    exact (functor_functorAdel_naturality α).symm
  slice_rhs 2 3 => rw [this]
  have : ((functor C).associator F.functorAdel (homologyLeftAbelian A)).inv ≫
      whiskerRight (whiskerLeft (functor C) (NatTrans.functorAdel α)) (homologyLeftAbelian A) =
      whiskerLeft (functor C) (whiskerRight (NatTrans.functorAdel α) (homologyLeftAbelian A))
      ≫ ((functor C).associator F'.functorAdel (homologyLeftAbelian A)).inv := by ext; simp
  slice_rhs 1 2 => rw [this]
  simp only [assoc]

end Naturality

section Compat

variable (C) in
noncomputable def functor_homology_iso_id :
    (functor C).functorAdel ⋙ homologyLeftAbelian (Adel C) ≅ 𝟭 (Adel C) := by
  refine Quotient.natIsoLift _ ?_
  refine (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Quotient.lift.isLift _
    ((functor C).mapComposableArrows 2 ⋙ Adel.quotient _) (functorAdel_aux (functor C))) _
    ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft ((functor C).mapComposableArrows 2)
    (Quotient.lift.isLift _ _ _) ≪≫ ?_ ≪≫ (Quotient.functor Adel.homotopic).rightUnitor.symm
  dsimp [homologyLeft]
  exact (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (contract_compat C)
    (ShortComplex.homologyFunctor (Adel C)) ≪≫ homology_iso_homology C ≪≫ homology_iso_id C

noncomputable def homologyLeftAbelien_comp_exact (G : Adel C ⥤ A)
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    G.functorAdel ⋙ homologyLeftAbelian A ≅ homologyLeftAbelian (Adel C) ⋙ G := by
  refine Quotient.natIsoLift _ ?_
  exact (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Quotient.lift.isLift _
    (G.mapComposableArrows 2 ⋙ quotient A) (functorAdel_aux G))
    (homologyLeftAbelian A) ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (G.mapComposableArrows 2) (quotient_homologyLeftAbelian A) ≪≫
    (Functor.associator _ _ _).symm  ≪≫ isoWhiskerRight (contractLeft_functoriality G)
    (ShortComplex.homologyFunctor A) ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft
    (contractLeft (Adel C)) (ShortComplex.homologyFunctorIso G) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight
    (quotient_homologyLeftAbelian (Adel C)).symm G ≪≫ Functor.associator _ _ _

lemma homologyLeftAbelien_comp_exact_naturality {G G': Adel C ⥤ A} [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (α : G ⟶ G') :
    whiskerRight (NatTrans.functorAdel α) (homologyLeftAbelian A) ≫
    (homologyLeftAbelien_comp_exact G').hom = (homologyLeftAbelien_comp_exact G).hom ≫
    whiskerLeft (homologyLeftAbelian (Adel C)) α := by
  dsimp [homologyLeftAbelien_comp_exact]
  refine Quotient.natTrans_ext _ _ ?_
  simp only [whiskerLeft_comp, whiskerLeft_natTransLift, whiskerLeft_twice, assoc]
  have :  whiskerLeft (Quotient.functor Adel.homotopic) (whiskerRight (NatTrans.functorAdel α)
      (homologyLeftAbelian A)) ≫ ((Quotient.functor Adel.homotopic).associator G'.functorAdel
      (homologyLeftAbelian A)).inv = ((Quotient.functor Adel.homotopic).associator
      G.functorAdel (homologyLeftAbelian A)).inv ≫ whiskerRight (whiskerLeft _
      (NatTrans.functorAdel α)) (homologyLeftAbelian A) := by aesop
  slice_lhs 1 2 => rw [this]
  have : whiskerRight (whiskerLeft (Quotient.functor Adel.homotopic) (NatTrans.functorAdel α))
      (homologyLeftAbelian A) ≫ whiskerRight (Quotient.lift.isLift Adel.homotopic
      (G'.mapComposableArrows 2 ⋙ quotient A) (functorAdel_aux G')).hom
      (homologyLeftAbelian A) = whiskerRight (Quotient.lift.isLift Adel.homotopic
      (G.mapComposableArrows 2 ⋙ quotient A) (functorAdel_aux G)).hom
      (homologyLeftAbelian A) ≫ whiskerRight (whiskerRight ((whiskeringRight (Fin 3) _ _).map α)
      (quotient A)) (homologyLeftAbelian A) := by
    rw [← whiskerRight_comp, whiskerRight_comp, ← whiskerRight_comp, ← whiskerRight_comp]
    congr 1
    dsimp [NatTrans.functorAdel]
    aesop
  slice_lhs 2 3 => rw [this]
  have : whiskerRight (whiskerRight ((whiskeringRight (Fin 3) (Adel C) A).map α) (quotient A))
      (homologyLeftAbelian A) ≫ ((G'.mapComposableArrows 2).associator (quotient A)
      (homologyLeftAbelian A)).hom = ((G.mapComposableArrows 2).associator (quotient A)
      (homologyLeftAbelian A)).hom ≫ whiskerRight ((whiskeringRight (Fin 3) (Adel C) A).map α)
      _ := by
    ext
    simp only [comp_obj, whiskeringRight_obj_obj, Nat.reduceAdd, whiskerRight_twice, assoc,
      NatTrans.comp_app, associator_hom_app, whiskerRight_app, Functor.comp_map, associator_inv_app,
      id_comp]
    erw [id_comp, comp_id]
  slice_lhs 3 4 => rw [this]
  have : whiskerRight ((whiskeringRight (Fin 3) (Adel C) A).map α) (quotient A ⋙
      homologyLeftAbelian A) ≫ whiskerLeft (G'.mapComposableArrows 2)
      (quotient_homologyLeftAbelian A).hom = whiskerLeft (G.mapComposableArrows 2)
      (quotient_homologyLeftAbelian A).hom ≫ whiskerRight ((whiskeringRight (Fin 3)
      (Adel C) A).map α) (homologyLeft A) := by
    dsimp [quotient_homologyLeftAbelian]
    ext
    simp only [comp_obj, whiskeringRight_obj_obj, NatTrans.comp_app, whiskerRight_app,
      Functor.comp_map, whiskerLeft_app, Quotient.lift.isLift_hom]
    erw [id_comp, comp_id]
    rfl
  slice_lhs 4 5 => rw [this]
  have :  whiskerRight ((whiskeringRight (Fin 3) (Adel C) A).map α) (homologyLeft A) ≫
      ((G'.mapComposableArrows 2).associator (contractLeft A)
      (ShortComplex.homologyFunctor A)).inv = ((G.mapComposableArrows 2).associator
      (contractLeft A) (ShortComplex.homologyFunctor A)).inv ≫ whiskerRight (whiskerRight
      ((whiskeringRight (Fin 3) (Adel C) A).map α) (contractLeft A))
      (ShortComplex.homologyFunctor A) := by
    ext
    dsimp
    erw [id_comp, comp_id]
    rfl
  slice_lhs 5 6 => rw [this]
  have : whiskerRight (whiskerRight ((whiskeringRight (Fin 3) (Adel C) A).map α)
      (contractLeft A)) (ShortComplex.homologyFunctor A) ≫ whiskerRight
      (contractLeft_functoriality G').hom (ShortComplex.homologyFunctor A) = whiskerRight
      (contractLeft_functoriality G).hom (ShortComplex.homologyFunctor A) ≫ whiskerRight
      (whiskerLeft (contractLeft (Adel C)) (NatTrans.mapShortComplex α))
      (ShortComplex.homologyFunctor A) := by
    rw [← whiskerRight_comp, whiskerRight_comp, ← whiskerRight_comp, ← whiskerRight_comp]
    congr 1
    exact contractLeft_functoriality_naturality α
  slice_lhs 6 7 => rw [this]
  have :  whiskerRight (whiskerLeft (contractLeft (Adel C)) (NatTrans.mapShortComplex α))
      (ShortComplex.homologyFunctor A) ≫ ((contractLeft (Adel C)).associator G'.mapShortComplex
      (ShortComplex.homologyFunctor A)).hom = ((contractLeft (Adel C)).associator
      G.mapShortComplex (ShortComplex.homologyFunctor A)).hom ≫ whiskerLeft
      (contractLeft (Adel C)) (whiskerRight (NatTrans.mapShortComplex α)
      (ShortComplex.homologyFunctor A)) := by aesop
  slice_lhs 7 8 => rw [this]
  have : whiskerLeft (contractLeft (Adel C)) (whiskerRight (NatTrans.mapShortComplex α)
      (ShortComplex.homologyFunctor A)) ≫ whiskerLeft (contractLeft (Adel C))
      (ShortComplex.homologyFunctorIso G').hom = whiskerLeft (contractLeft (Adel C))
      (ShortComplex.homologyFunctorIso G).hom ≫ whiskerLeft (contractLeft (Adel C))
      (whiskerLeft (ShortComplex.homologyFunctor (Adel C)) α) := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
    congr 1
    dsimp [NatTrans.mapShortComplex, ShortComplex.homologyFunctorIso]
    ext
    simp only [comp_obj, mapShortComplex_obj, ShortComplex.homologyFunctor_obj, NatTrans.comp_app,
      whiskerRight_app, ShortComplex.homologyFunctor_map, NatIso.ofComponents_hom_app,
      whiskerLeft_app]
    rw [NatTrans.app_homology]
    simp only [Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_right]
    rfl
  slice_lhs 8 9 => rw [this]
  have : whiskerLeft (contractLeft (Adel C)) (whiskerLeft (ShortComplex.homologyFunctor
      (Adel C)) α) ≫ ((contractLeft (Adel C)).associator (ShortComplex.homologyFunctor (Adel C))
      G').inv = ((contractLeft (Adel C)).associator (ShortComplex.homologyFunctor (Adel C))
      G).inv ≫ whiskerLeft _ α := by aesop
  slice_lhs 9 10 => rw [this]
  have : whiskerLeft (contractLeft (Adel C) ⋙ ShortComplex.homologyFunctor (Adel C)) α ≫
      whiskerRight (quotient_homologyLeftAbelian (Adel C)).inv G' = whiskerRight
      (quotient_homologyLeftAbelian (Adel C)).inv G ≫ whiskerLeft _ α := by aesop
  slice_lhs 10 11 => rw [this]
  simp [quotient]

noncomputable def liftAdel_unique (G : Adel C ⥤ A) [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] : (functor C ⋙ G).liftAdel ≅ G := by
  refine isoWhiskerRight ((functor C).functorAdel_comp G).symm (homologyLeftAbelian A) ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft ((functor C).functorAdel)
    (homologyLeftAbelien_comp_exact G)
    ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (functor_homology_iso_id C) G ≪≫
    G.leftUnitor

lemma liftAdel_unique_naturality {G G': Adel C ⥤ A} [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (α : G ⟶ G') :
    whiskerRight (NatTrans.functorAdel (whiskerLeft (functor C) α)) (homologyLeftAbelian A) ≫
    (liftAdel_unique G').hom = (liftAdel_unique G).hom ≫ α := by
  dsimp [liftAdel_unique]
  have : whiskerRight (NatTrans.functorAdel (whiskerLeft (functor C) α)) (homologyLeftAbelian A) ≫
      whiskerRight ((functor C).functorAdel_comp G').inv (homologyLeftAbelian A) =
      whiskerRight ((functor C).functorAdel_comp G).inv (homologyLeftAbelian A) ≫
      whiskerRight (whiskerLeft (functor C).functorAdel (NatTrans.functorAdel α))
      (homologyLeftAbelian A) := by
    rw [← whiskerRight_comp, ← whiskerRight_comp]
    congr 1
    rw [← cancel_epi ((functor C).functorAdel_comp G).hom, ← cancel_mono
      ((functor C).functorAdel_comp G').hom, Iso.hom_inv_id_assoc, assoc, assoc, Iso.inv_hom_id,
      comp_id]
    exact NatTrans.functorAdel_comp_naturality_right α
  slice_lhs 1 2 => rw [this]
  have : whiskerRight (whiskerLeft (functor C).functorAdel (NatTrans.functorAdel α))
      (homologyLeftAbelian A) ≫ ((functor C).functorAdel.associator G'.functorAdel
      (homologyLeftAbelian A)).hom = ((functor C).functorAdel.associator G.functorAdel
      (homologyLeftAbelian A)).hom ≫ whiskerLeft (functor C).functorAdel (whiskerRight
      (NatTrans.functorAdel α) (homologyLeftAbelian A)) := by
    ext; simp
  slice_lhs 2 3 => rw [this]
  have : whiskerLeft (functor C).functorAdel (whiskerRight (NatTrans.functorAdel α)
      (homologyLeftAbelian A)) ≫ whiskerLeft (functor C).functorAdel
      (homologyLeftAbelien_comp_exact G').hom = whiskerLeft (functor C).functorAdel
      (homologyLeftAbelien_comp_exact G).hom ≫ whiskerLeft (functor C).functorAdel
      (whiskerLeft (homologyLeftAbelian (Adel C)) α) := by
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
    congr 1
    exact homologyLeftAbelien_comp_exact_naturality α
  slice_lhs 3 4 => rw [this]
  have : whiskerLeft (functor C).functorAdel (whiskerLeft (homologyLeftAbelian (Adel C)) α) ≫
      ((functor C).functorAdel.associator (homologyLeftAbelian (Adel C)) G').inv =
      ((functor C).functorAdel.associator (homologyLeftAbelian (Adel C)) G).inv ≫
      whiskerLeft _ α := by ext; simp
  slice_lhs 4 5 => rw [this]
  have : whiskerLeft ((functor C).functorAdel ⋙ homologyLeftAbelian (Adel C)) α ≫
      whiskerRight (functor_homology_iso_id C).hom G' =
      whiskerRight (functor_homology_iso_id C).hom G ≫ whiskerLeft _ α := by ext; simp
  slice_lhs 5 6 => rw [this]
  have : whiskerLeft (𝟭 (Adel C)) α ≫ G'.leftUnitor.hom = G.leftUnitor.hom ≫ α := by ext; simp
  slice_lhs 6 7 => rw [this]
  simp

/-
-- Is this true ?

variable (F : C ⥤ A) [F.Additive]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

lemma unique_vs_isLift : (liftAdel_unique F.liftAdel).hom =
    whiskerRight (NatTrans.functorAdel F.liftAdelIsLift.hom) (homologyLeftAbelian A) := by
  dsimp [Functor.liftAdelIsLift]
  simp only [NatTrans.functorAdel_comp]
  dsimp [liftAdel_unique]
  refine Quotient.natTrans_ext _ _ ?_
  ext X
  dsimp
  simp only [comp_id, id_comp, map_comp]
  conv_rhs => congr; erw [NatTrans.functorAdel_id]; rw [NatTrans.id_app, Functor.map_id]; rfl
              congr; rfl; congr
              erw [NatTrans.functorAdel_id]; rw [NatTrans.id_app, Functor.map_id]; rfl
              congr; rfl
              erw [NatTrans.functorAdel_id]; rw [NatTrans.id_app, Functor.map_id]
  simp only [comp_id, id_comp]
  dsimp [NatTrans.functorAdel]
  simp only [map_comp, assoc]
  conv_rhs => congr; erw [Functor.map_id]; rfl; congr; rfl; congr; erw [Functor.map_id]; rfl;
              congr; erw [Functor.map_id]; rfl; congr; rfl; erw [Functor.map_id]
  simp only [comp_id, id_comp]
  have : (((functor C).functorAdel_comp F.liftAdel).inv.app
      ((Quotient.functor Adel.homotopic).obj X)) = 𝟙 _ := by
    dsimp [Functor.functorAdel_comp, whiskeringRightObjCompIso]
    simp only [comp_id, Functor.map_id]
    erw [Functor.map_id, comp_id]
    rfl
  rw [this, Functor.map_id]; erw [id_comp]
  dsimp [functor_homology_iso_id]
  simp only [comp_id, id_comp, map_comp]
  conv_lhs => congr; rfl; congr; erw [Functor.map_id, Functor.map_id]; rfl; congr
              erw [Functor.map_id]; rfl; congr; erw [Functor.map_id]
  simp only [id_comp]
  sorry
-/


end Compat

section TwoCat

namespace Adel

variable (C A)

noncomputable def lift_aux : (C ⥤+ A) ⥤ (Adel C ⥤ A) where
  obj F :=
    letI := F.2
    F.1.liftAdel
  map {F G} α :=
    letI := F.2
    letI := G.2
    Functor.whiskerRight (NatTrans.functorAdel α.hom) (homologyLeftAbelian A)
  map_id F := by
    ext
    simp only [comp_obj, whiskerRight_app, NatTrans.id_app]
    erw [NatTrans.functorAdel_id, Functor.map_id]
    rfl
  map_comp α β := by
    ext
    simp only [comp_obj, whiskerRight_app, NatTrans.comp_app]
    erw [NatTrans.functorAdel_comp, Functor.map_comp]

noncomputable def lift : (C ⥤+ A) ⥤ (Adel C ⥤ₑ A) :=
  ObjectProperty.lift _ (lift_aux C A)
  (fun F ↦ by refine ⟨?_, ?_⟩ <;> dsimp [lift_aux] <;> simp <;> infer_instance)

noncomputable def shrink_aux : (Adel C ⥤+ A) ⥤ (C ⥤+ A) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ {obj F := functor C ⋙ F, map u := whiskerLeft (functor C) u})
  (fun F ↦ by have := F.2; dsimp; rw [additiveFunctor_iff]; infer_instance)

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

noncomputable def shrink : (Adel C ⥤ₑ A) ⥤ (C ⥤+ A) :=
  AdditiveFunctor.ofExact (Adel C) A ⋙ shrink_aux C A

noncomputable def lift_shrink : lift C A ⋙ shrink C A ≅ 𝟭 (C ⥤+ A) := by
  refine NatIso.ofComponents (fun F ↦ ?_) (fun α ↦ ?_)
  · exact ObjectProperty.isoMk _ F.1.liftAdelIsLift
  · exact (ObjectProperty.ι _).map_injective (liftAdelIsLift_naturality α.hom)

noncomputable def shrink_lift : shrink C A ⋙ lift C A ≅ 𝟭 (Adel C ⥤ₑ A) := by
  refine NatIso.ofComponents (fun F ↦ ?_) (fun α ↦ ?_)
  · exact ObjectProperty.isoMk _ (liftAdel_unique F.1)
  · exact (ObjectProperty.ι _).map_injective (liftAdel_unique_naturality α.hom)

-- I don't know if the formula below gives an equivalence on the nose... :-()
/-
noncomputable def liftEquivalence : (C ⥤+ A) ≌ (Adel C ⥤ₑ A) where
  functor := lift C A
  inverse := shrink C A
  unitIso := (lift_shrink C A).symm
  counitIso := shrink_lift C A
  functor_unitIso_comp F := by
    refine (ObjectProperty.ι _).map_injective ?_
    dsimp [lift_shrink, shrink_lift, lift, lift_aux]
    rw [unique_vs_isLift]
    erw [← whiskerRight_comp]
    rw [← NatTrans.functorAdel_comp, Iso.inv_hom_id, NatTrans.functorAdel_id]
    erw [whiskerRight_id]
    rfl
-/

noncomputable def liftEquivalence : (Adel C ⥤ₑ A) ≌ (C ⥤+ A) :=
  Equivalence.mk (shrink C A) (lift C A) (shrink_lift C A).symm (lift_shrink C A)

@[simp]
lemma liftEquivalence_functor (G : Adel C ⥤ A) [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] :
    (liftEquivalence C A).functor.obj (ExactFunctor.of G) =
    AdditiveFunctor.of (functor C ⋙ G) := rfl

@[simp]
lemma liftEquivalence_inverse (F : C ⥤ A) [F.Additive] :
    (liftEquivalence C A).inverse.obj (AdditiveFunctor.of F) =
    ExactFunctor.of F.liftAdel := rfl

noncomputable def liftAdelUnique (F : C ⥤ A) [F.Additive] (G : Adel C ⥤ A) [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (e : (functor C) ⋙ G ≅ F) :
    G ≅ F.liftAdel :=
  (ObjectProperty.ι _).mapIso ((shrink_lift C A).symm.app (ExactFunctor.of G) ≪≫ (lift C A).mapIso
  (ObjectProperty.isoMk (fun F : C ⥤ A => F.Additive) e :
  (shrink C A).obj (ExactFunctor.of G) ≅ AdditiveFunctor.of F))

variable {C A} {G G' G'' : Adel C ⥤ A} [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] [PreservesFiniteLimits G'']
  [PreservesFiniteColimits G'']

lemma natTrans_ext (τ₁ τ₂ : G ⟶ G') (h : whiskerLeft (functor C) τ₁ = whiskerLeft (functor C) τ₂) :
    τ₁ = τ₂ := by
  suffices ({hom := τ₁} = ({hom := τ₂} : ExactFunctor.of G ⟶ ExactFunctor.of G')) by
    exact ObjectProperty.hom_ext_iff.mp this
  exact (liftEquivalence C A).functor.map_injective (InducedCategory.hom_ext h)

noncomputable def natTransLift (τ : functor C ⋙ G ⟶ functor C ⋙ G') : G ⟶ G' := by
  set α : (liftEquivalence C A).functor.obj (ExactFunctor.of G) ⟶
    (liftEquivalence C A).functor.obj (ExactFunctor.of G') := {hom := τ}
  exact ((liftEquivalence C A).functor.preimage α).hom

lemma natTransLift_whisker (τ : functor C ⋙ G ⟶ functor C ⋙ G') :
    whiskerLeft (functor C) (natTransLift τ) = τ := by
  suffices ({hom := whiskerLeft (functor C) (natTransLift τ)} = ({hom := τ} :
      AdditiveFunctor.of (functor C ⋙ G) ⟶ AdditiveFunctor.of (functor C ⋙ G'))) by
    exact ObjectProperty.hom_ext_iff.mp this
  exact (liftEquivalence C A).functor.map_preimage _

@[simp]
lemma natTransLift_app (τ : functor C ⋙ G ⟶ functor C ⋙ G') (X : C) :
    (natTransLift τ).app ((functor C).obj X) = τ.app X := by
  conv_rhs => rw [← natTransLift_whisker τ]
  simp

@[reassoc]
lemma comp_natTransLift (τ : functor C ⋙ G ⟶ functor C ⋙ G')
    (τ' : functor C ⋙ G' ⟶ functor C ⋙ G'') :
    natTransLift τ ≫ natTransLift τ' = natTransLift (τ ≫ τ') := by
  erw [← (exactFunctor (Adel C) A).hom_ext_iff]
  apply (liftEquivalence C A).functor.map_injective
  dsimp [natTransLift]
  erw [(liftEquivalence C A).functor.map_comp]
  simp only [Functor.map_preimage]
  rfl

@[simp]
lemma natTransLift_id : natTransLift (𝟙 (functor C ⋙ G)) = 𝟙 G := by
  erw [← (exactFunctor (Adel C) A).hom_ext_iff]
  apply (liftEquivalence C A).functor.map_injective
  dsimp [natTransLift]
  simp only [map_preimage]
  rfl

@[simps]
noncomputable def natIsoLift (τ : functor C ⋙ G ≅ functor C ⋙ G') : G ≅ G' where
  hom := natTransLift τ.hom
  inv := natTransLift τ.inv
  hom_inv_id := by rw [comp_natTransLift, τ.hom_inv_id, natTransLift_id]
  inv_hom_id := by rw [comp_natTransLift, τ.inv_hom_id, natTransLift_id]

end Adel

end TwoCat

end CategoryTheory
