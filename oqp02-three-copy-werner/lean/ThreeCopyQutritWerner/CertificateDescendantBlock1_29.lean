module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_29 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![-2, -2, 2, -2, -2, 2, -2, -2, 2, 2, 2, 0, 0, 0, 2;
     2, 0, 0, 2, 0, 0, 2, 0, 0, -2, 0, 0, 0, 0, 2;
     0, 2, 0, 0, 2, 0, 0, 2, 0, 0, -2, 0, 0, 0, 2;
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, -6, -6;
     0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, -6, -6, 6, 4;
     2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -6, -6, 6, 4;
     -2, -2, 2, 0, 0, 0, 0, 0, 0, -2, -2, -6, -6, 6, 4;
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -6, 0, -6, -6;
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 6, 0, 6, 4;
     0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 6, 0, 6, 4;
     0, 0, 0, -2, -2, 2, 0, 0, 0, -2, -2, 6, 0, 6, 4;
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -6, -6, -6;
     0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 6, 6, 4;
     0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 6, 6, 4;
     0, 0, 0, 0, 0, 0, -2, -2, 2, -2, -2, 0, 6, 6, 4]

def certificateDescendantBlockW1_29 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![-9, 54, -9, 54, -45, 144, -45, -9, 18, -45, 18, -9, 18, -45, 18;
     -9, -9, 54, 54, 144, -45, -45, -9, -45, 18, 18, -9, -45, 18, 18;
     36, 36, 36, 162, 54, 54, 54, -27, -9, -9, -9, -27, -9, -9, -9;
     -9, 54, -9, -9, 18, -45, 18, 54, -45, 144, -45, -9, 18, -45, 18;
     -9, -9, 54, -9, -45, 18, 18, 54, 144, -45, -45, -9, -45, 18, 18;
     36, 36, 36, -27, -9, -9, -9, 162, 54, 54, 54, -27, -9, -9, -9;
     -9, 54, -9, -9, 18, -45, 18, -9, 18, -45, 18, 54, -45, 144, -45;
     -9, -9, 54, -9, -45, 18, 18, -9, -45, 18, 18, 54, 144, -45, -45;
     36, 36, 36, -27, -9, -9, -9, -27, -9, -9, -9, 162, 54, 54, 54;
     21, -42, 21, 0, -21, 42, -21, 0, -21, 42, -21, 0, -21, 42, -21;
     21, 21, -42, 0, 42, -21, -21, 0, 42, -21, -21, 0, 42, -21, -21;
     0, 0, 0, 7, -7, -7, -7, -14, 14, 14, 14, 7, -7, -7, -7;
     0, 0, 0, 7, -7, -7, -7, 7, -7, -7, -7, -14, 14, 14, 14;
     -36, -36, -36, 20, 16, 16, 16, 20, 16, 16, 16, 20, 16, 16, 16;
     48, 48, 48, -36, -12, -12, -12, -36, -12, -12, -12, -36, -12, -12, -12]

/-- Exact integer inverse certificate for signed physical weight [2, -2, 0]. -/
theorem certificateDescendantBlock1_29_inverse :
    certificateDescendantBlockA1_29 * certificateDescendantBlockW1_29 =
      (504 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_29_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 29) := by decide

theorem certificateDescendantBlock1_29_row_weight (i : Fin 15) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 29 i) r) =
      certificateDescendantWeights1 29 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_29_column_weight (j : Fin 15) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 29)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 29 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_29_physical (i j : Fin 15) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 29 j))
      (certificateDescendantBlockRows1 29 i) = certificateDescendantBlockA1_29 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
