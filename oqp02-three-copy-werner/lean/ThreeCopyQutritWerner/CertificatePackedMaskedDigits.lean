module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.List.Enum
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-! A single exact masked-product equality can certify several distant binary
digits. The mask must retain every bit in the requested output digit. -/
namespace ThreeCopyQutritWerner

theorem certificatePackedMaskedDigit (x mask y shift width : ℕ)
    (h : x &&& mask = y)
    (hm : mask / 2 ^ shift % 2 ^ width = 2 ^ width - 1) :
    x / 2 ^ shift % 2 ^ width = y / 2 ^ shift % 2 ^ width := by
  have he := congrArg (fun z : ℕ => z / 2 ^ shift % 2 ^ width) h
  rw [Nat.and_div_two_pow, Nat.and_mod_two_pow, hm,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod] at he
  exact he

theorem certificatePackedMaskedNestedDigit (x mask y outerShift outerWidth
    innerShift innerWidth : ℕ) (h : x &&& mask = y)
    (hm : (mask / 2 ^ outerShift % 2 ^ outerWidth) /
      2 ^ innerShift % 2 ^ innerWidth = 2 ^ innerWidth - 1) :
    (x / 2 ^ outerShift % 2 ^ outerWidth) / 2 ^ innerShift % 2 ^ innerWidth =
      (y / 2 ^ outerShift % 2 ^ outerWidth) / 2 ^ innerShift % 2 ^ innerWidth := by
  have he := congrArg (fun z : ℕ =>
    (z / 2 ^ outerShift % 2 ^ outerWidth) / 2 ^ innerShift % 2 ^ innerWidth) h
  simp only [Nat.and_div_two_pow, Nat.and_mod_two_pow] at he
  rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod] at he
  exact he

end ThreeCopyQutritWerner
