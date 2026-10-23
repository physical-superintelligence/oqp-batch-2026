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


/-! The corrected residual block `222-0` of the h sector (2 x 2),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `222-0` (over `X2Nh.den`). -/
def nh_222k0 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1232120133297489983883864912871881973623442019064764447067340800, 821413422198326655922576608581254649082294679376509631378227200;
    821413422198326655922576608581254649082294679376509631378227200, 547608948132217770615051072387503099388196452917673087585484800]

end ThreeCopyQutritWerner.X2Nh
