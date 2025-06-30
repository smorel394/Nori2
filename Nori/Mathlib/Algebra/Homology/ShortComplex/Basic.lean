import Mathlib.Algebra.Homology.ShortComplex.Basic

open CategoryTheory Category Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F F' : C ⥤ D} [F.PreservesZeroMorphisms] [F'.PreservesZeroMorphisms] (α : F ⟶ F')

def NatTrans.mapShortComplex : F.mapShortComplex ⟶ F'.mapShortComplex where
  app X := ShortComplex.homMk (α.app X.X₁) (α.app X.X₂) (α.app X.X₃) (α.naturality _).symm
    (α.naturality _).symm
