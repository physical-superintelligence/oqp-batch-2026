module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_01 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![120]

def certificateDescendantBlockW2_01 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

/-- Exact integer inverse certificate for signed physical weight [-5, 1, 0]. -/
theorem certificateDescendantBlock2_01_inverse :
    certificateDescendantBlockA2_01 * certificateDescendantBlockW2_01 =
      (120 : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_01_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 1) := by decide

theorem certificateDescendantBlock2_01_row_weight (i : Fin 1) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 1 i) r) =
      certificateDescendantWeights2 1 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_01_column_weight (j : Fin 1) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 1)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 1 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_01_physical (i j : Fin 1) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 1 j))
      (certificateDescendantBlockRows2 1 i) = certificateDescendantBlockA2_01 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
