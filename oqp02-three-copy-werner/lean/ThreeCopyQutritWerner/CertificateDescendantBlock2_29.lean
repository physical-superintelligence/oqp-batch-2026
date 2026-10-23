module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_29 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, 0, -1, 0, 0, -2, -2, -6;
     0, 0, 0, -1, 0, 0, -2, 0, -2, -6;
     0, 0, -1, 0, 0, 0, -2, -2, 0, -6;
     0, -1, 0, 0, 0, -2, 0, 0, -2, -6;
     -1, 0, 0, 0, 0, -2, 0, -2, 0, -6;
     1, 1, 1, 1, 1, -2, -2, 0, 0, -6;
     0, 1, 0, 1, 1, 2, 2, 2, 0, -6;
     1, 0, 1, 0, 1, 2, 2, 0, 2, -6;
     -1, -1, 0, 0, -1, 2, 0, 2, 2, -6;
     0, 0, -1, -1, -1, 0, 2, 2, 2, -6]

def certificateDescendantBlockW2_29 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![10, -10, 10, 10, -30, 10, -10, 10, -10, 10;
     10, 10, -10, -30, 10, 10, 10, -10, -10, 10;
     10, 10, -30, -10, 10, 10, -10, 10, 10, -10;
     10, -30, 10, 10, -10, 10, 10, -10, 10, -10;
     -30, 10, 10, 10, 10, -10, 10, 10, -10, -10;
     4, 4, 4, -6, -6, -6, 4, 4, 4, -6;
     4, -6, -6, 4, 4, -6, 4, 4, -6, 4;
     -6, 4, -6, 4, -6, 4, 4, -6, 4, 4;
     -6, -6, 4, -6, 4, 4, -6, 4, 4, 4;
     -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]

/-- Exact integer inverse certificate for signed physical weight [1, -3, -2]. -/
theorem certificateDescendantBlock2_29_inverse :
    certificateDescendantBlockA2_29 * certificateDescendantBlockW2_29 =
      (60 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_29_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 29) := by decide

theorem certificateDescendantBlock2_29_row_weight (i : Fin 10) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 29 i) r) =
      certificateDescendantWeights2 29 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_29_column_weight (j : Fin 10) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 29)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 29 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_29_physical (i j : Fin 10) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 29 j))
      (certificateDescendantBlockRows2 29 i) = certificateDescendantBlockA2_29 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
