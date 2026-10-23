module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.List.Enum
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


open scoped Matrix
namespace ThreeCopyQutritWerner

def certificateDescendantFrames1SourceSize : Fin 8 → ℕ := ![1,
    2,
    2,
    9,
    7,
    7,
    17,
    6]

def certificateDescendantFrames2SourceSize : Fin 7 → ℕ := ![1,
    4,
    5,
    5,
    15,
    10,
    11]

end ThreeCopyQutritWerner
