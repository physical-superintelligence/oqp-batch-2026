module

public import Mathlib.Logic.Equiv.Fin.Basic
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


namespace ThreeCopyQutritWerner
def certificateTripleSourceIndex (a b c : ℕ) :
    Fin (a * (b * c)) ≃ (Fin a × Fin b × Fin c) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)
end ThreeCopyQutritWerner
