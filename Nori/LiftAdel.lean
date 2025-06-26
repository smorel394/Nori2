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

noncomputable def liftAdelIsLift : functor C ⋙ F.liftAdel ≅ F := by
  dsimp [Functor.liftAdel, functor]
  set e : quotient C ⋙ F.functorAdel ≅ F.mapComposableArrows 2 ⋙ Adel.quotient A :=
    (Quotient.lift.isLift homotopic (F.mapComposableArrows 2 ⋙ Adel.quotient A)
    (functorAdel_aux F)).symm
  refine Functor.associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft (functor_aux C) ((Functor.associator _ _ _).symm ≪≫
    (isoWhiskerRight e (homologyLeftAbelian A)) ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (F.mapComposableArrows 2) (quotient_homologyLeftAbelian A))
    ≪≫ ?_
  refine (Functor.associator _ _ _).symm ≪≫ ?_
  refine isoWhiskerRight F.functor_mapComposableArrows (homologyLeft A) ≪≫ ?_
  refine Functor.associator _ _ _ ≪≫ ?_
  refine isoWhiskerLeft F (functor_homologyLeft A) ≪≫ F.rightUnitor

end Functor

end CategoryTheory
