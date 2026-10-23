module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_21 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![6]

def certificateDescendantBlockW1_21 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

/-- Exact integer inverse certificate for signed physical weight [0, 3, -3]. -/
theorem certificateDescendantBlock1_21_inverse :
    certificateDescendantBlockA1_21 * certificateDescendantBlockW1_21 =
      (6 : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_21_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 21) := by decide

theorem certificateDescendantBlock1_21_row_weight (i : Fin 1) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 21 i) r) =
      certificateDescendantWeights1 21 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_21_column_weight (j : Fin 1) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 21)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 21 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_21_physical (i j : Fin 1) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 21 j))
      (certificateDescendantBlockRows1 21 i) = certificateDescendantBlockA1_21 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
