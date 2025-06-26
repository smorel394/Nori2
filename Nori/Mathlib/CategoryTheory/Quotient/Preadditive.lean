import Mathlib.CategoryTheory.Quotient.Preadditive

namespace CategoryTheory

universe u v u' v'

namespace Quotient

variable {C : Type u} [Category.{v} C] [Preadditive C] (r : HomRel C) [Congruence r]
  (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y), r f₁ f₂ → r g₁ g₂ → r (f₁ + g₁) (f₂ + g₂))
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive] (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

lemma lift_additive :
    letI := preadditive r hr
    (Quotient.lift r F H).Additive := by
  letI := preadditive r hr
  have := functor_additive r hr
  have : (functor r ⋙ lift r F H).Additive :=
    Functor.additive_of_iso (Quotient.lift.isLift r F H).symm
  exact Functor.additive_of_full_essSurj_comp (functor r) _

end Quotient

end CategoryTheory
