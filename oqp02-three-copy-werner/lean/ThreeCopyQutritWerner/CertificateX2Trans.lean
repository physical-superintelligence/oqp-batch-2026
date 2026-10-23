module

public import ThreeCopyQutritWerner.CertificateX2PackedLiteral
public import Mathlib.Data.Matrix.Basic
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


/-! Data: exact parity-coordinate transfer blocks `Q_s = N₀ R_s⁻¹ Niₛ`
(s = 1, 2; diagonal blocks S 282 x 282 and A 231 x 231) as numerators over `qden_s`
(57153600 for s = 1, 6350400 for s = 2), stored with offset 2^31. -/

namespace ThreeCopyQutritWerner.X2

x2_nat_table transS1Tab "verification/matrix-literals/x2-transfer/trans/S1.hex"
x2_nat_table transA1Tab "verification/matrix-literals/x2-transfer/trans/A1.hex"
x2_nat_table transS2Tab "verification/matrix-literals/x2-transfer/trans/S2.hex"
x2_nat_table transA2Tab "verification/matrix-literals/x2-transfer/trans/A2.hex"

/-- Offset numerator rows of the S block (`s = 1, 2`; empty otherwise). -/
noncomputable def transSRows (s : ℕ) : List (List ℕ) :=
  if s = 1 then transS1Tab else if s = 2 then transS2Tab else []

/-- Offset numerator rows of the A block. -/
noncomputable def transARows (s : ℕ) : List (List ℕ) :=
  if s = 1 then transA1Tab else if s = 2 then transA2Tab else []

/-- The common denominator `qden_s`. -/
def transDen (s : ℕ) : ℕ := if s = 1 then 57153600 else if s = 2 then 6350400 else 1

/-- Exact numerator `Snum_s[i][j]`. -/
noncomputable def transSNum (s i j : ℕ) : ℤ := (((transSRows s).getD i []).getD j 0 : ℤ) - 2 ^ 31

/-- Exact numerator `Anum_s[i][j]`. -/
noncomputable def transANum (s i j : ℕ) : ℤ := (((transARows s).getD i []).getD j 0 : ℤ) - 2 ^ 31

/-- `transS s` of the bridge's `X2Data` (s = 1, 2; zero for s = 0, unused). -/
noncomputable def x2TransS (s : Fin 3) : Matrix (Fin 282) (Fin 282) ℚ :=
  Matrix.of fun i j => if s.val = 0 then 0 else (transSNum s.val i.val j.val : ℚ) / (transDen s.val : ℚ)

/-- `transA s` of the bridge's `X2Data`. -/
noncomputable def x2TransA (s : Fin 3) : Matrix (Fin 231) (Fin 231) ℚ :=
  Matrix.of fun i j => if s.val = 0 then 0 else (transANum s.val i.val j.val : ℚ) / (transDen s.val : ℚ)

/-- Shapes, checked by the kernel. -/
theorem trans_shape : (transS1Tab.length == 282) && transS1Tab.all (·.length == 282) &&
    (transS2Tab.length == 282) && transS2Tab.all (·.length == 282) &&
    (transA1Tab.length == 231) && transA1Tab.all (·.length == 231) &&
    (transA2Tab.length == 231) && transA2Tab.all (·.length == 231) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2
