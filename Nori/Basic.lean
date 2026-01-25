import Mathlib.CategoryTheory.PathCategory.Basic
import Nori.Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Nori.Mathlib.CategoryTheory.Preadditive.Mat
import Nori.Mathlib.CategoryTheory.NatIso
import Nori.LiftAdel

universe u v u' v'

open CategoryTheory Category Functor Limits Adel

open scoped ZeroObject

attribute [local instance] Functor.additive_of_preserves_binary_products

variable (Q : Type u) [Quiver.{v + 1} Q]

namespace CategoryTheory

abbrev Ab := Adel (Mat_ (Free ℤ (Paths Q)))

namespace Ab

noncomputable abbrev embedding : Q ⥤q Ab Q :=
  Paths.of Q ⋙q (Free.embedding ℤ _ ⋙ Mat_.embedding _ ⋙ functor _).toPrefunctor

variable {Q}

variable {A : Type u} [Category.{max u v} A] [Abelian A]
--variable {A : Type u'} [Category.{v'} A] [Abelian A]

local instance : Limits.HasFiniteBiproducts A := Limits.HasFiniteBiproducts.of_hasFiniteProducts

noncomputable abbrev lift (T : Q ⥤q A) : Ab Q ⥤ A := liftAdel (Mat_.lift (Free.lift ℤ (Paths.lift T)))

variable (T : Q ⥤q A)

-- `Ab.lift T` is an additive exact functor.
#synth (lift T).Additive
#synth Limits.PreservesFiniteLimits (lift T)
#synth Limits.PreservesFiniteColimits (lift T)

def embeddingLiftIso : embedding Q ⋙q (lift T).toPrefunctor ≅ T := sorry

end Ab

end CategoryTheory
