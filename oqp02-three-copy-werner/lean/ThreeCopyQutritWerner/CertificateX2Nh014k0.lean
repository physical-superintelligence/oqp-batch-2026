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


/-! The corrected residual block `014-0` of the h sector (3 x 3),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `014-0` (over `X2Nh.den`). -/
def nh_014k0 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![12014228058352343065546135059462946377229199133934643618400, -24028456116704686131092270118925892754458398267869287236800, -31236992951716091970419951154603660580795917748230073407840;
    -24028456116704686131092270118925892754458398267869287236800, 48056912233409372262184540237851785508916796535738574473600, 62473985903432183940839902309207321161591835496460146815680;
    -31236992951716091970419951154603660580795917748230073407840, 62473985903432183940839902309207321161591835496460146815680, 81216181674461839123091873001969517510069386145398190860384]

end ThreeCopyQutritWerner.X2Nh
