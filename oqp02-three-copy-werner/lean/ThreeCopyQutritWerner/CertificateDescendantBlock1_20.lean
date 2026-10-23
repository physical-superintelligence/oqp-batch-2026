module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_20 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, 0, 0, 0, 0, 0, -2, -2, 2, 6, 6, 0, -1, 0, 2;
     0, 0, 0, 0, 0, 0, 2, 0, 0, -6, 0, 0, -1, 0, 2;
     0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -6, 0, -1, 0, 2;
     0, 0, 0, -2, -2, 2, 0, 0, 0, 6, 6, -1, 0, 0, 2;
     0, 0, 0, 2, 0, 0, 0, 0, 0, -6, 0, -1, 0, 0, 2;
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -6, -1, 0, 0, 2;
     -2, -2, 2, 0, 0, 0, 0, 0, 0, 6, 6, 1, 1, 0, 2;
     2, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 1, 1, 0, 2;
     0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -6, 1, 1, 0, 2;
     -2, -2, 2, -2, -2, 2, -2, -2, 2, -6, -6, 0, 0, -6, -6;
     2, 0, 0, 2, 0, 0, 2, 0, 0, 6, 0, 0, 0, -6, -6;
     0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 6, 0, 0, -6, -6;
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 6, 4;
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 6, 4;
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 6, 4]

def certificateDescendantBlockW1_20 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![18, -45, 18, 18, -45, 18, -45, 144, -45, -9, 54, -9, 54, -9, -9;
     18, 18, -45, 18, 18, -45, -45, -45, 144, -9, -9, 54, 54, -9, -9;
     -9, -9, -9, -9, -9, -9, 54, 54, 54, 36, 36, 36, 162, -27, -27;
     18, -45, 18, -45, 144, -45, 18, -45, 18, -9, 54, -9, -9, 54, -9;
     18, 18, -45, -45, -45, 144, 18, 18, -45, -9, -9, 54, -9, 54, -9;
     -9, -9, -9, 54, 54, 54, -9, -9, -9, 36, 36, 36, -27, 162, -27;
     -45, 144, -45, 18, -45, 18, 18, -45, 18, -9, 54, -9, -9, -9, 54;
     -45, -45, 144, 18, 18, -45, 18, 18, -45, -9, -9, 54, -9, -9, 54;
     54, 54, 54, -9, -9, -9, -9, -9, -9, 36, 36, 36, -27, -27, 162;
     7, -14, 7, 7, -14, 7, 7, -14, 7, -7, 14, -7, 0, 0, 0;
     7, 7, -14, 7, 7, -14, 7, 7, -14, -7, -7, 14, 0, 0, 0;
     42, 42, 42, -84, -84, -84, 42, 42, 42, 0, 0, 0, -42, 84, -42;
     -84, -84, -84, 42, 42, 42, 42, 42, 42, 0, 0, 0, -42, -42, 84;
     -20, -20, -20, -20, -20, -20, -20, -20, -20, -4, -4, -4, 24, 24, 24;
     24, 24, 24, 24, 24, 24, 24, 24, 24, -12, -12, -12, -12, -12, -12]

/-- Exact integer inverse certificate for signed physical weight [0, 2, -2]. -/
theorem certificateDescendantBlock1_20_inverse :
    certificateDescendantBlockA1_20 * certificateDescendantBlockW1_20 =
      (504 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_20_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 20) := by decide

theorem certificateDescendantBlock1_20_row_weight (i : Fin 15) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 20 i) r) =
      certificateDescendantWeights1 20 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_20_column_weight (j : Fin 15) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 20)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 20 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_20_physical (i j : Fin 15) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 20 j))
      (certificateDescendantBlockRows1 20 i) = certificateDescendantBlockA1_20 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
