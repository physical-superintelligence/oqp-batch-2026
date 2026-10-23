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


/-! The corrected residual block `116-1` of the h sector (3 x 3),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `116-1` (over `X2Nh.den`). -/
def nh_116k1 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1106795556845639506982602717542826359835675007017795025155307520, 1543624358691050518706186904172667812393400768744987987226040320, 1504583276323902653227714911064307341129836668761971637712440320;
    1543624358691050518706186904172667812393400768744987987226040320, 11346053240387195856535088641042467589067189459049337550927192064, 2774367775193133918047770937119512798882924038785769362339094016;
    1504583276323902653227714911064307341129836668761971637712440320, 2774367775193133918047770937119512798882924038785769362339094016, 2096729699241419521437330413514803048506754395648953016319366784]

end ThreeCopyQutritWerner.X2Nh
