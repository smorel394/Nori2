import Nori.Functoriality
import Nori.HomologyExact
import Nori.Calculs

universe u v u' v'

open CategoryTheory Category Functor Limits Adel

open scoped ZeroObject

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
  ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft F (functor_homologyLeftAbelian A) ≪≫ F.leftUnitor

end Functor

section Naturality

variable {F F' : C ⥤ A} [F.Additive] [F'.Additive] (α : F ⟶ F')

lemma liftAdelIsLift_naturality : whiskerLeft (functor C)
    (whiskerRight (NatTrans.functorAdel α) (homologyLeftAbelian A)) ≫ F'.liftAdelIsLift.hom =
    F.liftAdelIsLift.hom ≫ α := by
  dsimp [Functor.liftAdelIsLift]
  simp only [assoc]
  have : whiskerLeft F (functor_homologyLeftAbelian A).hom ≫ F.leftUnitor.hom ≫ α =
      whiskerRight α (functor A ⋙ homologyLeftAbelian A) ≫ whiskerLeft F'
      (functor_homologyLeftAbelian A).hom ≫ F'.leftUnitor.hom := by
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

variable [HasFiniteBiproducts C]

local instance : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts _

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

attribute [local instance] Functor.additive_of_preserves_binary_products

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
    whiskerLeft (homologyLeftAbelian (Adel C)) α := sorry

noncomputable def liftAdel_unique (G : Adel C ⥤ A) [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (functor C ⋙ G).liftAdel ≅ G := by
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
    whiskerRight (NatTrans.functorAdel (α : F.1 ⟶ G.1)) (homologyLeftAbelian A)
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
  (fun F ↦ by refine ⟨?_, ?_⟩ <;> dsimp [lift_aux] <;> infer_instance)

noncomputable def shrink_aux : (Adel C ⥤+ A) ⥤ (C ⥤+ A) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ {obj F := functor C ⋙ F, map u := whiskerLeft (functor C) u})
  (fun F ↦ by have := F.2; dsimp; infer_instance)

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

noncomputable def shrink : (Adel C ⥤ₑ A) ⥤ (C ⥤+ A) :=
  AdditiveFunctor.ofExact (Adel C) A ⋙ shrink_aux C A

noncomputable def lift_shrink : lift C A ⋙ shrink C A ≅ 𝟭 (C ⥤+ A) := by
  refine NatIso.ofComponents (fun F ↦ ?_) (fun α ↦ ?_)
  · exact ObjectProperty.isoMk _ F.1.liftAdelIsLift
  · exact (ObjectProperty.ι _).map_injective (liftAdelIsLift_naturality α)

noncomputable def shrink_lift : shrink C A ⋙ lift C A ≅ 𝟭 (Adel C ⥤ₑ A) := by
  refine NatIso.ofComponents (fun F ↦ ?_) (fun α ↦ ?_)
  · exact ObjectProperty.isoMk _ (liftAdel_unique F.1)
  · exact (ObjectProperty.ι _).map_injective (liftAdel_unique_naturality α)

end Adel

end TwoCat

end CategoryTheory
