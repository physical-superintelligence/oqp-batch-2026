module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_09 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2880, 2880, 720;
     -2880, 0, 720;
     0, -2880, 720]

def certificateDescendantBlockW1_09 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 1;
     1, 1, -2;
     4, 4, 4]

/-- Exact integer inverse certificate for signed physical weight [-1, -2, 3]. -/
theorem certificateDescendantBlock1_09_inverse :
    certificateDescendantBlockA1_09 * certificateDescendantBlockW1_09 =
      (8640 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_09_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 9) := by decide

theorem certificateDescendantBlock1_09_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 9 i) r) =
      certificateDescendantWeights1 9 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_09_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 9)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 9 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_09_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 9 j))
      (certificateDescendantBlockRows1 9 i) = certificateDescendantBlockA1_09 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
