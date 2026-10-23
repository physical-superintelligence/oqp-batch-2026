module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_24 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/a5e5d94e312bf6ef9ad3c7b6bad887065508fe29269d44d21c298878c2caac72.xz" "6eb6d9d824b26e960a99464fca0aaa9c1f75aaaecdae6a4344643f226c600161"

def certificateDescendantBlockW2_24 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/89ac9289b335d6c6fc43769405b79831c1caac621387f61efec87a6c50bd7a01.xz" "80ac75ff0865727304e5b51c8e8e4979904d761bee5c49b4c73daf78eb9acbc3"

/-- Exact integer inverse certificate for signed physical weight [0, -1, -3]. -/
theorem certificateDescendantBlock2_24_inverse :
    certificateDescendantBlockA2_24 * certificateDescendantBlockW2_24 =
      (2520 : ℤ) • (1 : Matrix (Fin 35) (Fin 35) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_24_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 24) := by decide

theorem certificateDescendantBlock2_24_row_weight (i : Fin 35) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 24 i) r) =
      certificateDescendantWeights2 24 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_24_column_weight (j : Fin 35) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 24)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 24 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_24_physical (i j : Fin 35) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 24 j))
      (certificateDescendantBlockRows2 24 i) = certificateDescendantBlockA2_24 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
