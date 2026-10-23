module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_19 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/75515fba110045eddb48697e2bd6c04ac72eef96a41a7fe86fce5f3b4bc2d521.xz" "ad6b4071d02c335d3603202791329c002bbc30d5cb003f604562abafdcafdc0c"

def certificateDescendantBlockW1_19 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/d795a4522492af111c0a8bcb06fb6116dd6925f73f2bd7079dd847f2bcd279cf.xz" "accfa7233dd4e77d1da34c4feefb58d830cc9cd6f9abfd9fd1aa640a37970a2a"

/-- Exact integer inverse certificate for signed physical weight [0, 1, -1]. -/
theorem certificateDescendantBlock1_19_inverse :
    certificateDescendantBlockA1_19 * certificateDescendantBlockW1_19 =
      (15120 : ℤ) • (1 : Matrix (Fin 60) (Fin 60) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_19_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 19) := by decide

theorem certificateDescendantBlock1_19_row_weight (i : Fin 60) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 19 i) r) =
      certificateDescendantWeights1 19 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_19_column_weight (j : Fin 60) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 19)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 19 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_19_physical (i j : Fin 60) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 19 j))
      (certificateDescendantBlockRows1 19 i) = certificateDescendantBlockA1_19 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
