module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_14 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![24, 24, 6;
     -24, 0, 6;
     0, -24, 6]

def certificateDescendantBlockW1_14 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 1;
     1, 1, -2;
     4, 4, 4]

/-- Exact integer inverse certificate for signed physical weight [-1, 3, -2]. -/
theorem certificateDescendantBlock1_14_inverse :
    certificateDescendantBlockA1_14 * certificateDescendantBlockW1_14 =
      (72 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_14_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 14) := by decide

theorem certificateDescendantBlock1_14_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 14 i) r) =
      certificateDescendantWeights1 14 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_14_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 14)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 14 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_14_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 14 j))
      (certificateDescendantBlockRows1 14 i) = certificateDescendantBlockA1_14 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
