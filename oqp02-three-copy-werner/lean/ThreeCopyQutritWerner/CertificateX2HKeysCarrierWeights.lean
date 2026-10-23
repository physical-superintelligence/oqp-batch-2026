module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.List.Enum
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-! a literal copy of the sector-0 carrier weights (`certificateCarrierNumerator0`,
`certificateCarrierDenominator0`, `certificateCarrierWeight0`; CertificateCarrierPermutations). -/

namespace ThreeCopyQutritWerner.X2Sites

def x2hNum : Fin 120 → ℤ :=
  ![4,
    -4,
    -4,
    4,
    2,
    -2,
    -2,
    2,
    2,
    -2,
    -2,
    2,
    -2,
    2,
    2,
    -2,
    4,
    -4,
    -4,
    4,
    -2,
    2,
    2,
    -2,
    2,
    -2,
    -2,
    2,
    1,
    -1,
    -1,
    1,
    -1,
    1,
    1,
    -1,
    -2,
    2,
    2,
    -2,
    -1,
    1,
    1,
    -1,
    -1,
    1,
    1,
    -1,
    2,
    -2,
    -2,
    2,
    -1,
    1,
    1,
    -1,
    -1,
    1,
    1,
    -1,
    2,
    -2,
    -2,
    2,
    -1,
    1,
    1,
    -1,
    -1,
    1,
    1,
    -1,
    -1,
    1,
    1,
    -1,
    2,
    -2,
    -2,
    2,
    -1,
    1,
    1,
    -1,
    -2,
    2,
    2,
    -2,
    -1,
    1,
    1,
    -1,
    2,
    -2,
    -2,
    2,
    -1,
    1,
    1,
    -1,
    -1,
    1,
    1,
    -1,
    -1,
    1,
    1,
    -1,
    -2,
    2,
    2,
    -2,
    -1,
    1,
    1,
    -1,
    -1,
    1,
    1,
    -1]

def x2hDen : ℕ := 96

def x2hWeight (p : Fin 120) : ℚ :=
  x2hNum p / x2hDen

end ThreeCopyQutritWerner.X2Sites
