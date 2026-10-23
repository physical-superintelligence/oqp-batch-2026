module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_32 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

def certificateDescendantBlockW2_32 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

/-- Exact integer inverse certificate for signed physical weight [1, 0, -5]. -/
theorem certificateDescendantBlock2_32_inverse :
    certificateDescendantBlockA2_32 * certificateDescendantBlockW2_32 =
      (1 : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_32_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 32) := by decide

theorem certificateDescendantBlock2_32_row_weight (i : Fin 1) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 32 i) r) =
      certificateDescendantWeights2 32 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_32_column_weight (j : Fin 1) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 32)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 32 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_32_physical (i j : Fin 1) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 32 j))
      (certificateDescendantBlockRows2 32 i) = certificateDescendantBlockA2_32 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
