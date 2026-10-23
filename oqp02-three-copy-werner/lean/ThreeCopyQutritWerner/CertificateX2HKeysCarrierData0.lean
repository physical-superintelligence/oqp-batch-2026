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


/-! a literal copy of the sector-0 carrier action on type 0
(`certificateCarrierAction0_0`, CertificateCarrierActionData0_0; for the pinned payloads the decoded
literal text, as the `certificate_matrix` elaborator produces it), and the traces of its first three powers
(`x2hTr0 j p = trace (A_p ^ (j + 1))`, checked by the kernel in CertificateX2HKeysTrCheck0). Data only. -/

open scoped Matrix

namespace ThreeCopyQutritWerner.X2Sites

noncomputable def x2hA0 : Fin 120 → Matrix (Fin 1) (Fin 1) ℤ :=
  ![!![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1],
    !![1]]

noncomputable def x2hTr0 : Fin 3 → Fin 120 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

end ThreeCopyQutritWerner.X2Sites
