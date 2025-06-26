import Mathlib.CategoryTheory.Limits.Shapes.Kernels

universe u v u' v'

open CategoryTheory Category Limits

variable {C : Type u} [Category.{v, u} C] [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y}
  {D : Type u'} [Category.{v, u'} D] [HasZeroMorphisms D] (F : Functor C D)
  [F.PreservesZeroMorphisms]

-- Remove unnecessary hypothesis on `F`
def CategoryTheory.Limits.compNatIso' : (parallelPair f 0).comp F ≅ parallelPair (F.map f) 0 := by
  refine NatIso.ofComponents (fun j ↦ ?_) (fun u ↦ ?_)
  · match j with
    | WalkingParallelPair.zero => exact Iso.refl _
    | WalkingParallelPair.one => exact Iso.refl _
  · match u with
    | WalkingParallelPairHom.id _ => dsimp; simp
    | WalkingParallelPairHom.left => dsimp; simp
    | WalkingParallelPairHom.right => dsimp; simp
