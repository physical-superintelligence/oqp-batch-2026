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


/-! The common denominator of the corrected h-block literals `X2Nh.nh_<kk>`. -/

namespace ThreeCopyQutritWerner.X2Nh

/-- Common denominator of the 122 corrected residual blocks: `2^176 3^9 5^4 7^2`. -/
def den : ℕ := 57735991281730516779464839149788173726453690037306728120320000

/-- The same denominator as an integer. -/
def denInt : ℤ := 57735991281730516779464839149788173726453690037306728120320000

end ThreeCopyQutritWerner.X2Nh
