module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_30 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 1, 1, 1, 0, 1, 1, 1, 2;
     1, 1, 0, 0, 1, 1, 0, 1, 1, 2;
     -1, 0, -1, 0, -1, 1, 1, 0, 1, 2;
     0, -1, 0, -1, -1, 1, 1, 1, 0, 2;
     -1, -1, -1, -1, -1, -1, -1, 0, 0, 2;
     1, 0, 0, 0, 0, -1, 0, -1, 0, 2;
     0, 1, 0, 0, 0, -1, 0, 0, -1, 2;
     0, 0, 1, 0, 0, 0, -1, -1, 0, 2;
     0, 0, 0, 1, 0, 0, -1, 0, -1, 2;
     0, 0, 0, 0, 1, 0, 0, -1, -1, 2]

def certificateDescendantBlockW2_30 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-10, 10, -10, 10, -10, 30, -10, -10, 10, -10;
     -10, 10, 10, -10, -10, -10, 30, 10, -10, -10;
     10, -10, -10, 10, -10, -10, 10, 30, -10, -10;
     10, -10, 10, -10, -10, 10, -10, -10, 30, -10;
     10, 10, -10, -10, 10, -10, -10, -10, -10, 30;
     -12, 8, 8, 8, -12, -12, -12, 8, 8, 8;
     8, -12, 8, 8, -12, 8, 8, -12, -12, 8;
     8, 8, -12, 8, 8, -12, 8, -12, 8, -12;
     8, 8, 8, -12, 8, 8, -12, 8, -12, -12;
     3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

/-- Exact integer inverse certificate for signed physical weight [1, -2, -3]. -/
theorem certificateDescendantBlock2_30_inverse :
    certificateDescendantBlockA2_30 * certificateDescendantBlockW2_30 =
      (60 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_30_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 30) := by decide

theorem certificateDescendantBlock2_30_row_weight (i : Fin 10) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 30 i) r) =
      certificateDescendantWeights2 30 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_30_column_weight (j : Fin 10) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 30)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 30 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_30_physical (i j : Fin 10) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 30 j))
      (certificateDescendantBlockRows2 30 i) = certificateDescendantBlockA2_30 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
