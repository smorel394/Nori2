import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.ComposableArrows

universe u v

open CategoryTheory Category Functor Limits

open scoped ZeroObject

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CategoryTheory

namespace Adel

open ComposableArrows

abbrev zero : Fin 3 := ⟨0, by omega⟩
abbrev one : Fin 3 := ⟨1, by omega⟩
abbrev two : Fin 3 := ⟨2, by omega⟩

def homotopic : HomRel (ComposableArrows C 2) :=
  fun X Y u v ↦ ∃ (σ₁ : X.obj one ⟶ Y.obj zero) (σ₂ : X.obj two ⟶ Y.obj one),
                u.app one = (σ₁ ≫ Y.map' 0 1) + (X.map' 1 2 ≫ σ₂) + v.app one

instance : Congruence (homotopic (C := C)) where
  equivalence := by
    refine {refl u := ?_, symm h := ?_, trans h h' := ?_}
    · exact ⟨0, 0, by simp⟩
    · obtain ⟨σ₁, σ₂, eq⟩ := h
      use -σ₁, -σ₂
      rw [eq]
      dsimp
      simp only [Fin.isValue, homOfLE_leOfHom, Preadditive.neg_comp, Preadditive.comp_neg]
      abel
    · obtain ⟨σ₁, σ₂, eq⟩ := h
      obtain ⟨σ₁', σ₂', eq'⟩ := h'
      use σ₁ + σ₁', σ₂ + σ₂'
      rw [eq, eq']
      dsimp
      simp only [Fin.isValue, homOfLE_leOfHom, Preadditive.add_comp, Preadditive.comp_add]
      abel
  compLeft u _ _ h := by
    obtain ⟨σ₁, σ₂, eq⟩ := h
    use u.app one ≫ σ₁, u.app two ≫ σ₂
    rw [NatTrans.comp_app, eq]
    dsimp
    simp only [Fin.isValue, homOfLE_leOfHom, Preadditive.comp_add, assoc, add_left_inj,
      add_right_inj]
    conv_lhs => rw [← assoc, ← NatTrans.naturality, assoc]
    rfl
  compRight v h := by
    obtain ⟨σ₁, σ₂, eq⟩ := h
    use σ₁ ≫ v.app zero, σ₂ ≫ v.app one
    rw [NatTrans.comp_app, eq]
    dsimp
    simp only [Fin.isValue, homOfLE_leOfHom, Preadditive.add_comp, assoc, NatTrans.naturality]

end Adel

open Adel

variable (C) in
def Adel := Quotient (homotopic (C := C))

namespace Adel

instance : Category (Adel C) := by
  dsimp [Adel]
  infer_instance

variable (C) in
def quotient : ComposableArrows C 2 ⥤ Adel C := Quotient.functor (homotopic (C := C))

theorem quotient_map_eq_iff {X Y : ComposableArrows C 2} (u v : X ⟶ Y) :
    (quotient C).map u = (quotient C).map v ↔ homotopic u v :=
  Quotient.functor_map_eq_iff _ _ _

instance : (quotient C).Full := Quotient.full_functor _

instance : (quotient C).EssSurj := Quotient.essSurj_functor _

-- Is this useful? It's very evil.
lemma quotient_obj_surjective (X : Adel C) :
    ∃ (K : ComposableArrows C 2), (quotient _).obj K = X :=
  ⟨_, rfl⟩

instance : Preadditive (Adel C) := Quotient.preadditive _ (by
  rintro _ _ _ _ _ _ ⟨σ₁, σ₂, eq⟩ ⟨σ₁', σ₂', eq'⟩
  use σ₁ + σ₁', σ₂ + σ₂'
  rw [NatTrans.app_add, NatTrans.app_add, eq, eq']
  dsimp
  simp only [Fin.isValue, homOfLE_leOfHom, Preadditive.add_comp, Preadditive.comp_add]
  abel)

instance : (quotient C).Additive where

section ZeroObject

instance [HasZeroObject C] : HasZeroObject (Adel C) where
  zero := by
    use (quotient C).obj 0
    rw [IsZero.iff_id_eq_zero, ← (quotient C).map_id, id_zero, (quotient C).map_zero]

end ZeroObject

section Biproducts

variable [HasFiniteBiproducts C]

instance : HasFiniteProducts (ComposableArrows C 2) := by
  dsimp [ComposableArrows]
  infer_instance

instance : HasFiniteBiproducts (ComposableArrows C 2) :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance : HasFiniteProducts (Adel C) where
  out n := by
    refine {has_limit F := HasLimit.mk ?_}
    set g : Fin n → ComposableArrows C 2 := fun j ↦ (quotient C).objPreimage (F.obj {as := j})
    set ι : Discrete.functor g ⋙ (quotient C) ≅ F :=
      Discrete.natIso (fun _ ↦ (quotient C).objObjPreimageIso _)
    refine {cone := ?_, isLimit := ?_}
    · exact (Cones.postcompose ι.hom).obj ((quotient C).mapCone (limit.cone (Discrete.functor g)))
    · exact (IsLimit.postcomposeHomEquiv _ _).invFun (isLimitOfPreserves (quotient C)
        (limit.isLimit _))

instance : HasFiniteBiproducts (Adel C) := HasFiniteBiproducts.of_hasFiniteProducts

instance : HasBinaryBiproducts (ComposableArrows C 2) := hasBinaryBiproducts_of_finite_biproducts _

instance : HasBinaryBiproducts (Adel C) := hasBinaryBiproducts_of_finite_biproducts _

end Biproducts

section Duality

open Opposite

variable (C) in
def duality_aux : (ComposableArrows C 2)ᵒᵖ ≌ ComposableArrows (Cᵒᵖ) 2 :=
  (Functor.opUnopEquiv (Fin 3) C).trans (Equivalence.congrLeft
  ((orderDualEquivalence (Fin 3)).symm.trans (OrderIso.equivalence Fin.revOrderIso)))

variable (C) in
def quotientOp : ComposableArrows (Cᵒᵖ) 2 ⥤ (Adel C)ᵒᵖ :=
  (duality_aux C).inverse ⋙ (quotient C).op

instance : (quotientOp C).Full := by
  dsimp [quotientOp]
  infer_instance

instance : (quotientOp C).EssSurj := by
  dsimp [quotientOp]
  infer_instance

lemma quotientOp_map_eq_iff {X Y : ComposableArrows (Cᵒᵖ) 2} (u v : X ⟶ Y) :
    homotopic u v ↔ (quotientOp C).map u = (quotientOp C).map v := sorry

variable (C) in
def duality_functor : Adel (Cᵒᵖ) ⥤ (Adel C)ᵒᵖ :=
  Quotient.lift _ (quotientOp C) (fun _ _ _ _ ↦ (quotientOp_map_eq_iff _ _).mp)

instance : (duality_functor C).Full := by
  have : (quotient (Cᵒᵖ) ⋙ duality_functor C).Full := Functor.Full.of_iso (Quotient.lift.isLift
    homotopic (quotientOp C)  (fun _ _ _ _ ↦ (quotientOp_map_eq_iff _ _).mp)).symm
  refine {map_surjective {X Y} u := ?_}
  set e := (quotient _).objObjPreimageIso X
  set f := (quotient _).objObjPreimageIso Y
  set v := (quotient (Cᵒᵖ) ⋙ duality_functor C).preimage
    ((duality_functor C).map e.hom ≫ u ≫ (duality_functor C).map f.inv)
  use e.inv ≫ (quotient _).map v ≫ f.hom
  dsimp
  simp only [map_comp]
  conv_lhs => congr; rfl; congr
              rw [← Functor.comp_map, map_preimage]
  simp

instance : (duality_functor C).EssSurj where
  mem_essImage X := by
    have : (quotient (Cᵒᵖ) ⋙ duality_functor C).EssSurj :=
      Functor.essSurj_of_iso (Quotient.lift.isLift homotopic (quotientOp C)
      (fun _ _ _ _ ↦ (quotientOp_map_eq_iff _ _).mp)).symm
    use (quotient (Cᵒᵖ)).obj ((quotient (Cᵒᵖ) ⋙ duality_functor C).objPreimage X)
    exact Nonempty.intro ((quotient (Cᵒᵖ) ⋙ duality_functor C).objObjPreimageIso X)

instance : (duality_functor C).Faithful where
  map_injective {X Y} := by
    intro u v eq
    set e := (quotient _).objObjPreimageIso X
    set f := (quotient _).objObjPreimageIso Y
    set u' := (quotient _).preimage (e.hom ≫ u ≫ f.inv)
    set v' := (quotient _).preimage (e.hom ≫ v ≫ f.inv)
    have h : homotopic u' v' := by
      rw [quotientOp_map_eq_iff]
      have g : quotient _ ⋙ duality_functor C ≅ quotientOp C :=
        (Quotient.lift.isLift homotopic (quotientOp C)
        (fun _ _ _ _ ↦ (quotientOp_map_eq_iff _ _).mp))
      rw [← cancel_epi (g.hom.app _), ← NatTrans.naturality, Functor.comp_map, map_preimage,
        map_comp, map_comp, eq, ← map_comp, ← map_comp, ← NatTrans.naturality, Functor.comp_map,
        map_preimage]
    have := (quotient_map_eq_iff _ _).mpr h
    rw [map_preimage, map_preimage] at this
    simp only [Iso.cancel_iso_inv_right_assoc, Iso.cancel_iso_hom_left] at this
    exact this

instance : (duality_functor C).IsEquivalence where

/-variable (C) in
def duality : (Adel C)ᵒᵖ ≌ Adel (Cᵒᵖ) where
  functor := by
    refine Functor.leftOp (Quotient.lift _ ((duality_aux C).rightOp.functor ⋙
      (quotient Cᵒᵖ).op) (fun _ _ _ _ h ↦ ?_))
    obtain ⟨σ₁, σ₂, eq⟩ := h
    dsimp
    congr 1
    rw [quotient_map_eq_iff]
    use σ₂.op, σ₁.op
    dsimp [duality_aux] at eq ⊢
    erw [Quiver.Hom.unop_op, Quiver.Hom.unop_op]
    rw [eq]
    simp only [Fin.isValue, homOfLE_leOfHom, op_add, op_comp, add_left_inj]
    rw [add_comm]
    rfl
  inverse := by
    refine Quotient.lift _ ((duality_aux C).inverse ⋙ (quotient C).op) (fun _ _ _ _ h ↦ ?_)
    obtain ⟨σ₁, σ₂, eq⟩ := h
    dsimp
    congr 1
    rw [quotient_map_eq_iff]
    use σ₂.unop, σ₁.unop
    dsimp [duality_aux] at eq ⊢
    rw [eq]
    simp only [Fin.isValue, homOfLE_leOfHom, unop_add, unop_comp, add_left_inj]
    rw [add_comm]
    rfl
  unitIso := by
    refine NatIso.removeOp ?_
    refine ?_ ≪≫ (Functor.opId _).symm
    sorry
/-    refine Quotient.natIsoLift _ ?_
    refine NatIso.ofComponents (fun X ↦ ?_) ?_
    dsimp
    set Y := ((Quotient.lift homotopic ((duality_aux C).rightOp.functor ⋙
      (quotient Cᵒᵖ).op) sorry).obj (unop X))
-/
--    refine ?_ ≪≫ (Quotient.lift homotopic ((duality_aux C).rightOp.functor ⋙ (quotient Cᵒᵖ).op) sorry).mapIso ?_
  counitIso := sorry
-/

end Duality

section Cokernels

variable [HasBinaryBiproducts C]

namespace CandidateCoker

variable {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y')

noncomputable abbrev candcoker : ComposableArrows C 2 :=
  ComposableArrows.mk₂ (biprod.map (Y'.map' 0 1) (X'.map' 1 2) +
  biprod.snd ≫ u'.app one ≫ biprod.inl) (biprod.map (Y'.map' 1 2) (𝟙 (X'.obj two)))

noncomputable abbrev candπ : Y' ⟶ candcoker u' := by
  refine ComposableArrows.homMk₂ biprod.inl biprod.inl biprod.inl ?_ ?_
  · dsimp
    simp only [Fin.isValue, homOfLE_leOfHom, Preadditive.comp_add, biprod.inl_map]
    rw [biprod.inl_snd_assoc]
    simp only [Fin.isValue, homOfLE_leOfHom, zero_comp, add_zero]
    rfl
  · dsimp
    change _ = biprod.inl ≫ biprod.map _ _
    simp

lemma candcondition : homotopic (u' ≫ candπ u') 0 := by
  use biprod.inr, -biprod.inr
  dsimp
  simp only [Fin.isValue, homOfLE_leOfHom, Preadditive.comp_add, biprod.inr_map,
    BinaryBicone.inr_snd_assoc, Preadditive.comp_neg, add_zero]
  rw [add_assoc]; erw [add_add_neg_cancel'_right]
  rfl

lemma candepi {T : ComposableArrows C 2} (v : candcoker u' ⟶ T) (hv : homotopic (candπ u' ≫ v) 0) :
    homotopic v 0 := by
  obtain ⟨σ₁, σ₂, eq⟩ := hv
  use biprod.desc σ₁ 0, biprod.desc σ₂ (biprod.inr ≫ v.app one)
  dsimp at eq
  simp only [Fin.isValue, homOfLE_leOfHom, add_zero] at eq
  rw [NatTrans.app_zero, add_zero]
  change _ = _ + (biprod.map (Y'.map' 1 2) (𝟙 (X'.obj two))) ≫ _
  exact biprod.hom_ext' _ _ (by simp [eq]) (by simp)

instance : Epi ((quotient C).map (candπ u')) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro T v hv
  set e := (quotient C).objObjPreimageIso T
  set v' := (quotient C).preimage (v ≫ e.inv)
  have hv' : homotopic (candπ u' ≫ v') 0 := by
    rw [← quotient_map_eq_iff]
    dsimp [v']
    rw [map_comp, Functor.map_zero, map_preimage, ← assoc, hv, zero_comp]
  have : (quotient C).map v' = 0 := (quotient_map_eq_iff _ _).mpr (candepi u' v' hv')
  dsimp [v'] at this
  rw [(quotient C).map_preimage] at this
  simp only [Preadditive.IsIso.comp_right_eq_zero] at this
  exact this

noncomputable abbrev canddesc {T : ComposableArrows C 2} (v : Y' ⟶ T) (hv : homotopic (u' ≫ v) 0) :
    candcoker u' ⟶ T := by
  set σ₁ := hv.choose
  set σ₂ := hv.choose_spec.choose
  set eq : _ = σ₁ ≫ _ + _ ≫ σ₂ + _ := hv.choose_spec.choose_spec
  dsimp at eq
  simp only [Fin.isValue, homOfLE_leOfHom, add_zero] at eq
  refine ComposableArrows.homMk₂ (biprod.desc (v.app zero) σ₁) (biprod.desc (v.app one) (- σ₂))
    (biprod.desc (v.app two) (- σ₂ ≫ T.map' 1 2)) ?_ ?_
  · exact biprod.hom_ext' _ _ (by dsimp; simp) (by dsimp; simp [eq])
  · change biprod.map (Y'.map' 1 2) (𝟙 (X'.obj two)) ≫ _ = _
    exact biprod.hom_ext' _ _ (by dsimp [two]; simp) (by dsimp; simp)

lemma candfac {T : ComposableArrows C 2} (v : Y' ⟶ T) (hv : homotopic (u' ≫ v) 0) :
    candπ u' ≫ canddesc u' v hv = v := by
  refine ComposableArrows.hom_ext₂ ?_ ?_ ?_
  · dsimp [canddesc]; simp
  · dsimp [canddesc]; simp
  · dsimp
    change biprod.inl ≫ biprod.desc (v.app two) (- hv.choose_spec.choose ≫ T.map' 1 2) = _
    simp [two]

end CandidateCoker

open CandidateCoker

noncomputable def cocone_aux {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y') :
    Cocone (parallelPair u' 0 ⋙ quotient C) := by
  refine (Cocones.precompose (diagramIsoParallelPair (parallelPair u' 0 ⋙ quotient C)).hom).obj
    (Cofork.ofπ ((quotient C).map (candπ u')) ?_)
  suffices eq : (quotient C).map (u' ≫ (candπ u')) = (quotient C).map 0 by
    dsimp at eq ⊢
    simp only [map_comp, map_preimage, Category.assoc, Functor.map_zero,
      Preadditive.IsIso.comp_left_eq_zero, zero_comp] at eq ⊢
    exact eq
  exact (quotient_map_eq_iff _ _).mpr (candcondition u')

noncomputable abbrev π' {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y')
    (c : Cocone (parallelPair u' 0 ⋙ quotient C)) : Y' ⟶ (quotient C).objPreimage c.pt :=
  (quotient C).preimage (c.ι.app WalkingParallelPair.one ≫
  ((quotient C).objObjPreimageIso c.pt).inv)

omit [HasBinaryBiproducts C] in
lemma condition' {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y')
    (c : Cocone (parallelPair u' 0 ⋙ quotient C)) : homotopic (u' ≫ π' u' c) 0 := by
  rw [← quotient_map_eq_iff]
  dsimp [π']
  rw [map_comp,Functor.map_preimage, ← cancel_mono ((quotient C).objObjPreimageIso c.pt).hom]
  simp only [Nat.reduceAdd, assoc, Iso.inv_hom_id, comp_id, Functor.map_zero, zero_comp]
  have := c.w WalkingParallelPairHom.left
  dsimp at this
  rw [this]
  have := c.w WalkingParallelPairHom.right
  dsimp at this
  rw [← this]
  simp

noncomputable def cocone_isColimit {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y') :
    IsColimit (cocone_aux u') where
  desc c := (quotient C).map (canddesc u' (π' u' c) (condition' u' c)) ≫
    ((quotient C).objObjPreimageIso c.pt).hom
  fac c j := by
    match j with
    | WalkingParallelPair.zero =>
      have eq := c.w WalkingParallelPairHom.right
      have eq' := (cocone_aux u').w WalkingParallelPairHom.right
      dsimp at eq eq'
      rw [← eq, ← eq']
      dsimp
      simp
    | WalkingParallelPair.one =>
      have := candfac u' (π' u' c) (condition' u' c)
      dsimp [cocone_aux]
      simp only [Fin.isValue, homOfLE_leOfHom, id_comp]
      rw [← assoc, ← (quotient C).map_comp, this]
      dsimp [π']
      rw [(quotient C).map_preimage]
      simp
  uniq c m hm := by
    rw [← cancel_epi ((quotient C).map (candπ u'))]
    have := hm WalkingParallelPair.one
    dsimp [cocone_aux] at this
    simp only [Fin.isValue, homOfLE_leOfHom, id_comp] at this
    rw [this, ← assoc, ← (quotient C).map_comp, candfac u' (π' u' c) (condition' u' c)]
    dsimp [π']
    rw [(quotient C).map_preimage]
    simp

instance {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y') :
    HasColimit (parallelPair u' 0 ⋙ quotient C) :=
  HasColimit.mk {cocone := cocone_aux u', isColimit := cocone_isColimit u'}

open WalkingParallelPair WalkingParallelPairHom in
noncomputable instance {X Y : Adel C} (u : X ⟶ Y) : HasColimit (parallelPair u 0) := by
  set X' := (quotient C).objPreimage X
  set Y' := (quotient C).objPreimage Y
  set u' := (quotient C).preimage (((quotient C).objObjPreimageIso X).hom ≫ u ≫
    ((quotient C).objObjPreimageIso Y).inv)
  set g : WalkingParallelPair ⥤ ComposableArrows C 2 := parallelPair u' 0
  set ι : g ⋙ quotient C ≅ parallelPair u 0 := by
    refine NatIso.ofComponents (fun j ↦ ?_) (fun u ↦ ?_)
    · match j with
      | .zero => exact (quotient C).objObjPreimageIso X
      | .one => exact (quotient C).objObjPreimageIso Y
    · match u with
      | .id _ => dsimp; simp
      | .left => dsimp [g]; rw [(quotient C).map_preimage]; simp
      | .right => dsimp [g]; simp
  rw [← hasColimit_iff_of_iso ι]
  infer_instance

end Cokernels

section Kernels
/-
The existence of kernels follows from that of cokernels by duality, but we prove it
explicitly, since we will use the precise form of the kernel to prove that every
epimorphism is normal.
-/

variable [HasBinaryBiproducts C]

namespace CandidateKer

variable {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y')

noncomputable abbrev candker : ComposableArrows C 2 :=
  ComposableArrows.mk₂ (biprod.map (X'.map' 0 1) (𝟙 (Y'.obj zero)))
  (biprod.map (X'.map' 1 2) (Y'.map' 0 1) + biprod.fst ≫ u'.app one ≫ biprod.inr)

noncomputable abbrev candι : candker u' ⟶ X' := by
  refine ComposableArrows.homMk₂ biprod.fst biprod.fst biprod.fst ?_ ?_
  · dsimp; simp
  · change (biprod.map (X'.map' 1 2) (Y'.map' 0 1) + biprod.fst ≫ u'.app one ≫ biprod.inr) ≫ _ = _
    dsimp; simp

lemma candcondition : homotopic (candι u' ≫ u') 0 := by
  use -biprod.snd, biprod.snd
  change _ = _ + (biprod.map (X'.map' 1 2) (Y'.map' 0 1) + biprod.fst ≫ u'.app one ≫
    biprod.inr) ≫ _ + _
  dsimp
  simp

lemma candmono {T : ComposableArrows C 2} (v : T ⟶ candker u') (hv : homotopic (v ≫ candι u') 0) :
    homotopic v 0 := by
  obtain ⟨σ₁, σ₂, eq⟩ := hv
  use σ₁ ≫ biprod.inl + v.app one ≫ biprod.snd ≫ biprod.inr, σ₂ ≫ biprod.inl
  dsimp at eq
  simp only [Fin.isValue, homOfLE_leOfHom, add_zero] at eq
  rw [NatTrans.app_zero, add_zero]
  dsimp
  exact biprod.hom_ext _ _ (by simp [eq]) (by simp)

instance : Mono ((quotient C).map (candι u')) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T v hv
  set e := (quotient C).objObjPreimageIso T
  set v' := (quotient C).preimage (e.hom ≫ v)
  have hv' : homotopic (v' ≫ candι u') 0 := by
    rw [← quotient_map_eq_iff]
    dsimp [v']
    rw [map_comp, Functor.map_zero, map_preimage, assoc, hv, comp_zero]
  have : (quotient C).map v' = 0 := (quotient_map_eq_iff _ _).mpr (candmono u' v' hv')
  dsimp [v'] at this
  rw [(quotient C).map_preimage] at this
  simp only [Preadditive.IsIso.comp_left_eq_zero] at this
  exact this

noncomputable abbrev candlift {T : ComposableArrows C 2} (v : T ⟶ X') (hv : homotopic (v ≫ u') 0) :
    T ⟶ candker u' := by
  set σ₁ := hv.choose
  set σ₂ := hv.choose_spec.choose
  set eq : _ = σ₁ ≫ _ + _ ≫ σ₂ + _ := hv.choose_spec.choose_spec
  dsimp at eq
  simp only [Fin.isValue, homOfLE_leOfHom, add_zero] at eq
  refine ComposableArrows.homMk₂ (biprod.lift (v.app zero) (-T.map' 0 1 ≫ σ₁))
    (biprod.lift (v.app one) (-σ₁)) (biprod.lift (v.app two) σ₂) ?_ ?_
  · refine biprod.hom_ext _ _ (by dsimp; simp) (by dsimp; simp)
  · change _ = _ ≫ (biprod.map (X'.map' 1 2) (Y'.map' 0 1) + biprod.fst ≫ u'.app one ≫ biprod.inr)
    refine biprod.hom_ext _ _ ?_ ?_
    · dsimp
      simp [two]
    · dsimp
      simp [eq]

lemma candfac {T : ComposableArrows C 2} (v : T ⟶ X') (hv : homotopic (v ≫ u') 0) :
    candlift u' v hv ≫ candι u' = v := by
  refine ComposableArrows.hom_ext₂ ?_ ?_ ?_
  · dsimp [candlift]; simp
  · dsimp [candlift]; simp
  · dsimp
    change biprod.lift (v.app two) hv.choose_spec.choose ≫ biprod.fst = _
    simp [two]

end CandidateKer

open CandidateKer

noncomputable def cone_aux {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y') :
    Cone (parallelPair u' 0 ⋙ quotient C) := by
  refine (Cones.postcompose (diagramIsoParallelPair (parallelPair u' 0 ⋙ quotient C)).inv).obj
    (Fork.ofι ((quotient C).map (candι u')) ?_)
  suffices eq : (quotient C).map (candι u' ≫ u') = (quotient C).map 0 by
    dsimp at eq ⊢
    simp only [Fin.isValue, homOfLE_leOfHom, map_comp, Functor.map_zero, comp_zero] at eq ⊢
    exact eq
  exact (quotient_map_eq_iff _ _).mpr (candcondition u')

noncomputable abbrev ι' {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y')
    (c : Cone (parallelPair u' 0 ⋙ quotient C)) : (quotient C).objPreimage c.pt ⟶ X' :=
  (quotient C).preimage (((quotient C).objObjPreimageIso c.pt).hom ≫
  c.π.app WalkingParallelPair.zero)

omit [HasBinaryBiproducts C] in
lemma conditionk' {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y')
    (c : Cone (parallelPair u' 0 ⋙ quotient C)) : homotopic (ι' u' c ≫ u') 0 := by
  rw [← quotient_map_eq_iff]
  dsimp [ι']
  rw [map_comp,Functor.map_preimage, ← cancel_epi ((quotient C).objObjPreimageIso c.pt).inv]
  simp only [Nat.reduceAdd, assoc, Iso.inv_hom_id_assoc, Functor.map_zero, comp_zero]
  have := c.w WalkingParallelPairHom.left
  dsimp at this
  rw [this]
  have := c.w WalkingParallelPairHom.right
  dsimp at this
  rw [← this]
  simp

noncomputable def cone_isLimit {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y') :
    IsLimit (cone_aux u') where
  lift c := ((quotient C).objObjPreimageIso c.pt).inv ≫
    (quotient C).map (candlift u' (ι' u' c) (conditionk' u' c))
  fac c j := by
    match j with
    | WalkingParallelPair.zero =>
      have := candfac u' (ι' u' c) (conditionk' u' c)
      dsimp [cone_aux]
      simp only [Fin.isValue, homOfLE_leOfHom, comp_id, assoc]
      rw [← (quotient C).map_comp, this]
      dsimp [ι']
      rw [(quotient C).map_preimage]
      simp
    | WalkingParallelPair.one =>
      have eq := c.w WalkingParallelPairHom.right
      have eq' := (cone_aux u').w WalkingParallelPairHom.left
      dsimp at eq eq'
      rw [← eq, ← eq']
      dsimp [cone_aux]
      simp only [Fin.isValue, homOfLE_leOfHom, comp_id, assoc, Functor.map_zero, comp_zero,
        Preadditive.IsIso.comp_left_eq_zero]
      rw [← map_comp, (quotient_map_eq_iff _ _).mpr (candcondition u')]
      simp
  uniq c m hm := by
    rw [← cancel_mono ((quotient C).map (candι u'))]
    have := hm WalkingParallelPair.zero
    dsimp [cone_aux] at this
    simp only [Fin.isValue, homOfLE_leOfHom, comp_id] at this
    rw [this, assoc, ← (quotient C).map_comp, candfac u' (ι' u' c) (conditionk' u' c)]
    dsimp [ι']
    rw [(quotient C).map_preimage]
    simp

instance {X' Y' : ComposableArrows C 2} (u' : X' ⟶ Y') :
    HasLimit (parallelPair u' 0 ⋙ quotient C) :=
  HasLimit.mk {cone := cone_aux u', isLimit := cone_isLimit u'}

open WalkingParallelPair WalkingParallelPairHom in
noncomputable instance {X Y : Adel C} (u : X ⟶ Y) : HasLimit (parallelPair u 0) := by
  set X' := (quotient C).objPreimage X
  set Y' := (quotient C).objPreimage Y
  set u' := (quotient C).preimage (((quotient C).objObjPreimageIso X).hom ≫ u ≫
    ((quotient C).objObjPreimageIso Y).inv)
  set g : WalkingParallelPair ⥤ ComposableArrows C 2 := parallelPair u' 0
  set ι : g ⋙ quotient C ≅ parallelPair u 0 := by
    refine NatIso.ofComponents (fun j ↦ ?_) (fun u ↦ ?_)
    · match j with
      | .zero => exact (quotient C).objObjPreimageIso X
      | .one => exact (quotient C).objObjPreimageIso Y
    · match u with
      | .id _ => dsimp; simp
      | .left => dsimp [g]; rw [(quotient C).map_preimage]; simp
      | .right => dsimp [g]; simp
  rw [← hasLimit_iff_of_iso ι]
  infer_instance

end Kernels

section NormalEpi



end NormalEpi

end Adel

end CategoryTheory
