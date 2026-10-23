module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_31 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![-1, -1, 1, -1, -1, 1, -1, -1, 1, 1, 1, 0, 0, 0, 1;
     1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1;
     -1, -1, 1, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, -1, -1;
     1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, -1, -1;
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, -1;
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 0;
     0, 0, 0, -1, -1, 1, 0, 0, 0, -1, -1, -1, 0, -1, -1;
     0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, -1;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, -1, -1;
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0;
     0, 0, 0, 0, 0, 0, -1, -1, 1, -1, -1, 0, -1, -1, -1;
     0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, -1, -1;
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, -1, -1, -1;
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0]

def certificateDescendantBlockW1_31 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![-3, 18, -3, -15, 48, -15, 18, 6, -15, 6, -3, 6, -15, 6, -3;
     -3, -3, 18, -15, -15, 48, 18, 6, 6, -15, -3, 6, 6, -15, -3;
     12, 12, 12, 18, 18, 18, 54, -3, -3, -3, -9, -3, -3, -3, -9;
     -3, 18, -3, 6, -15, 6, -3, -15, 48, -15, 18, 6, -15, 6, -3;
     -3, -3, 18, 6, 6, -15, -3, -15, -15, 48, 18, 6, 6, -15, -3;
     12, 12, 12, -3, -3, -3, -9, 18, 18, 18, 54, -3, -3, -3, -9;
     -3, 18, -3, 6, -15, 6, -3, 6, -15, 6, -3, -15, 48, -15, 18;
     -3, -3, 18, 6, 6, -15, -3, 6, 6, -15, -3, -15, -15, 48, 18;
     12, 12, 12, -3, -3, -3, -9, -3, -3, -3, -9, 18, 18, 18, 54;
     7, -14, 7, -7, 14, -7, 0, -7, 14, -7, 0, -7, 14, -7, 0;
     7, 7, -14, -7, -7, 14, 0, -7, -7, 14, 0, -7, -7, 14, 0;
     0, 0, 0, 7, 7, 7, -7, -14, -14, -14, 14, 7, 7, 7, -7;
     0, 0, 0, 7, 7, 7, -7, 7, 7, 7, -7, -14, -14, -14, 14;
     -12, -12, -12, -4, -4, -4, 16, -4, -4, -4, 16, -4, -4, -4, 16;
     16, 16, 16, -4, -4, -4, -12, -4, -4, -4, -12, -4, -4, -4, -12]

/-- Exact integer inverse certificate for signed physical weight [2, 0, -2]. -/
theorem certificateDescendantBlock1_31_inverse :
    certificateDescendantBlockA1_31 * certificateDescendantBlockW1_31 =
      (84 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_31_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 31) := by decide

theorem certificateDescendantBlock1_31_row_weight (i : Fin 15) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 31 i) r) =
      certificateDescendantWeights1 31 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_31_column_weight (j : Fin 15) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 31)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 31 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_31_physical (i j : Fin 15) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 31 j))
      (certificateDescendantBlockRows1 31 i) = certificateDescendantBlockA1_31 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
