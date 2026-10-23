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


/-! The corrected residual block `115-1` of the h sector (2 x 2),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `115-1` (over `X2Nh.den`). -/
def nh_115k1 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![275216614152881778393469221993287270908552859565359087993018880, -68804153538220444598367305498321817727138214891339771998254720;
    -68804153538220444598367305498321817727138214891339771998254720, 17201038384555111149591826374580454431784553722834942999563680]

end ThreeCopyQutritWerner.X2Nh
