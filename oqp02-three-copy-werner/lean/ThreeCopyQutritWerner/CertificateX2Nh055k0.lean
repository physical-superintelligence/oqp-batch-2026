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


/-! The corrected residual block `055-0` of the h sector (3 x 3),
numerators over the common denominator `X2Nh.den` (CertificateX2NhDen), in the certificate's quadratic-form
J coordinates.
= T - out1 - out2 for the trial plus correction c-v1 (offline exact, quotient coordinates 0). -/

set_option maxRecDepth 100000

namespace ThreeCopyQutritWerner.X2Nh

/-- Corrected residual numerators of h block `055-0` (over `X2Nh.den`). -/
def nh_055k0 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![6880665628930284312900722241364606823422662496636009641048577920, 1949949183931315084469125561678501182233771361335353732053861120, -24819326742525118781681233551045638046427880872120701715584000;
    1949949183931315084469125561678501182233771361335353732053861120, 798224905385667674218447540363899052519535940540895653519889920, 375039104408231900131307035375620222926490858025680469007001600;
    -24819326742525118781681233551045638046427880872120701715584000, 375039104408231900131307035375620222926490858025680469007001600, 594424974298371897440558158829207297017398170649778819217817600]

end ThreeCopyQutritWerner.X2Nh
