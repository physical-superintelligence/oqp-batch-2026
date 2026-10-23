module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_26 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

def certificateDescendantBlockW2_26 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

/-- Exact integer inverse certificate for signed physical weight [0, 1, -5]. -/
theorem certificateDescendantBlock2_26_inverse :
    certificateDescendantBlockA2_26 * certificateDescendantBlockW2_26 =
      (1 : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_26_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 26) := by decide

theorem certificateDescendantBlock2_26_row_weight (i : Fin 1) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 26 i) r) =
      certificateDescendantWeights2 26 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_26_column_weight (j : Fin 1) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 26)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 26 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_26_physical (i j : Fin 1) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 26 j))
      (certificateDescendantBlockRows2 26 i) = certificateDescendantBlockA2_26 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
