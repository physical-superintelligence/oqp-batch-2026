module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_04 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -576, -288;
     -576, 0, -288;
     576, 576, -288]

def certificateDescendantBlockW1_04 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 1;
     -2, 1, 1;
     -2, -2, -2]

/-- Exact integer inverse certificate for signed physical weight [-2, -1, 3]. -/
theorem certificateDescendantBlock1_04_inverse :
    certificateDescendantBlockA1_04 * certificateDescendantBlockW1_04 =
      (1728 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_04_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 4) := by decide

theorem certificateDescendantBlock1_04_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 4 i) r) =
      certificateDescendantWeights1 4 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_04_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 4)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 4 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_04_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 4 j))
      (certificateDescendantBlockRows1 4 i) = certificateDescendantBlockA1_04 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
