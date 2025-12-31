import Mathlib.CategoryTheory.Quotient

open CategoryTheory Category Quotient

variable {C D : Type*} [Category C] [Category D] (r : HomRel C) {F G : Quotient r ⥤ D}
  (τ : (functor r).comp F ⟶ (functor r).comp G)

@[simp]
lemma whiskerLeft_natTransLift : (functor r).whiskerLeft (natTransLift r τ) = τ := by aesop
