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


/-! The corrected residual block `025-0` of the h sector (3 x 3),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `025-0` (over `X2Nh.den`). -/
def nh_025k0 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![621105911461911910646128479881693546497482123209747481729024, 465829433596433932984596359911270159873111592407310611296768, -1086935345058345843630724839792963706370593715617058093025792;
    465829433596433932984596359911270159873111592407310611296768, 349372075197325449738447269933452619904833694305482958472576, -815201508793759382723043629844722779777945286712793569769344;
    -1086935345058345843630724839792963706370593715617058093025792, -815201508793759382723043629844722779777945286712793569769344, 1902136853852105226353768469637686486148539002329851662795136]

end ThreeCopyQutritWerner.X2Nh
