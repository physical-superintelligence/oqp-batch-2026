module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_22 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 120, -240;
     120, 0, -240;
     -120, -120, -240]

def certificateDescendantBlockW1_22 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-2, 4, -2;
     4, -2, -2;
     -1, -1, -1]

/-- Exact integer inverse certificate for signed physical weight [1, -3, 2]. -/
theorem certificateDescendantBlock1_22_inverse :
    certificateDescendantBlockA1_22 * certificateDescendantBlockW1_22 =
      (720 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_22_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 22) := by decide

theorem certificateDescendantBlock1_22_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 22 i) r) =
      certificateDescendantWeights1 22 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_22_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 22)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 22 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_22_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 22 j))
      (certificateDescendantBlockRows1 22 i) = certificateDescendantBlockA1_22 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
