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


/-! The corrected residual block `044-1` of the h sector (3 x 3),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `044-1` (over `X2Nh.den`). -/
def nh_044k1 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![402124786012189337693818781091940655553673274490895136691687168, 0, -179690930279995146570190844256554558687994511029397891256860416;
    0, 0, 0;
    -179690930279995146570190844256554558687994511029397891256860416, 0, 111488385753517928755861794628466778187725025784187068855900928]

end ThreeCopyQutritWerner.X2Nh
