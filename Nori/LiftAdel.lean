import Nori.Functoriality
import Nori.HomologyExact

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

section Compat

variable [HasFiniteBiproducts C]

local instance : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts _

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


end CategoryTheory
