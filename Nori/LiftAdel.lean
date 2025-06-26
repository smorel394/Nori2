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

end CategoryTheory
