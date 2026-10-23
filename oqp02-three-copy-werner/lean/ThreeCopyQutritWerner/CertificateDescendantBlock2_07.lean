module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_07 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/ef85d8d162307fa58a12af970fa639ba8278441689b21413e27958c27609899d.xz" "50b76bd98c23c82663d52056d49ead00ffe013c580e8cc4426967dc072ccf6c8"

def certificateDescendantBlockW2_07 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/d767d7e2fd6709906d29230114ba8818d2e4bbc897927ad71092f4878088aa4c.xz" "41a1f3a0490e6becd625f966b3f8e82cb56976797d27c77d38bc588c57669a9e"

/-- Exact integer inverse certificate for signed physical weight [-3, 0, -1]. -/
theorem certificateDescendantBlock2_07_inverse :
    certificateDescendantBlockA2_07 * certificateDescendantBlockW2_07 =
      (15120 : ℤ) • (1 : Matrix (Fin 35) (Fin 35) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_07_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 7) := by decide

theorem certificateDescendantBlock2_07_row_weight (i : Fin 35) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 7 i) r) =
      certificateDescendantWeights2 7 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_07_column_weight (j : Fin 35) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 7)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 7 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_07_physical (i j : Fin 35) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 7 j))
      (certificateDescendantBlockRows2 7 i) = certificateDescendantBlockA2_07 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
