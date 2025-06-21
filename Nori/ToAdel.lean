import Nori.Adel

universe u v u' v'

open CategoryTheory Category Functor Limits

open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CategoryTheory

namespace Adel

noncomputable def functor_aux : C ⥤ ComposableArrows C 2 where
  obj X := ComposableArrows.mk₂ (0 : 0 ⟶ X) (0 : X ⟶ 0)
  map f := ComposableArrows.homMk₂ 0 f 0 (by simp) (by change _ = f ≫ 0; simp)
  map_id X := by
    refine ComposableArrows.hom_ext₂ (by simp) (by simp) ?_
    change 0 = 𝟙 0
    simp
  map_comp f g := by
    refine ComposableArrows.hom_ext₂ (by simp) (by simp) ?_
    change 0 = 0 ≫ 0
    simp

noncomputable def functor : C ⥤ Adel C := functor_aux C ⋙ quotient C

section Lift

variable {C} {A : Type u'} [Category.{v'} A] [Abelian A] (F : C ⥤ A)

def lift : Adel C ⥤ A := sorry

end Lift

end Adel

end CategoryTheory
