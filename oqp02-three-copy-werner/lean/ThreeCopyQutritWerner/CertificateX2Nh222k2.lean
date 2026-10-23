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


/-! The corrected residual block `222-2` of the h sector (2 x 2),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `222-2` (over `X2Nh.den`). -/
def nh_222k2 : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1772269953265327896561573251557298590085805063134438276606853120, 1291386786299972958862470656734165291132753582378812533784576000;
    1291386786299972958862470656734165291132753582378812533784576000, 1320590785801636652043287480930880258362439802314776092454657064960]

end ThreeCopyQutritWerner.X2Nh
