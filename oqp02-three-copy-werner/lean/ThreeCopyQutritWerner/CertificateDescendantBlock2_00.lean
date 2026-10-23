module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_00 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![120]

def certificateDescendantBlockW2_00 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

/-- Exact integer inverse certificate for signed physical weight [-5, 0, 1]. -/
theorem certificateDescendantBlock2_00_inverse :
    certificateDescendantBlockA2_00 * certificateDescendantBlockW2_00 =
      (120 : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_00_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 0) := by decide

theorem certificateDescendantBlock2_00_row_weight (i : Fin 1) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 0 i) r) =
      certificateDescendantWeights2 0 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_00_column_weight (j : Fin 1) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 0)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 0 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_00_physical (i j : Fin 1) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 0 j))
      (certificateDescendantBlockRows2 0 i) = certificateDescendantBlockA2_00 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
