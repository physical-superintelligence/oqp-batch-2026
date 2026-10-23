module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_28 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![24, 24, -24;
     -24, 0, -24;
     0, -24, -24]

def certificateDescendantBlockW1_28 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 1;
     1, 1, -2;
     -1, -1, -1]

/-- Exact integer inverse certificate for signed physical weight [2, -3, 1]. -/
theorem certificateDescendantBlock1_28_inverse :
    certificateDescendantBlockA1_28 * certificateDescendantBlockW1_28 =
      (72 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_28_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 28) := by decide

theorem certificateDescendantBlock1_28_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 28 i) r) =
      certificateDescendantWeights1 28 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_28_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 28)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 28 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_28_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 28 j))
      (certificateDescendantBlockRows1 28 i) = certificateDescendantBlockA1_28 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
