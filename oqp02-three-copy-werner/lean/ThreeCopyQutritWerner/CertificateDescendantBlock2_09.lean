module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_09 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, -144, -144, -144, 0, -48, -48, -48, -48;
     -144, -144, 0, 0, -144, -48, 0, -48, -48, -48;
     144, 0, 144, 0, 144, -48, -48, 0, -48, -48;
     0, 144, 0, 144, 144, -48, -48, -48, 0, -48;
     144, 144, 144, 144, 144, 48, 48, 0, 0, -48;
     -144, 0, 0, 0, 0, 48, 0, 48, 0, -48;
     0, -144, 0, 0, 0, 48, 0, 0, 48, -48;
     0, 0, -144, 0, 0, 0, 48, 48, 0, -48;
     0, 0, 0, -144, 0, 0, 48, 0, 48, -48;
     0, 0, 0, 0, -144, 0, 0, 48, 48, -48]

def certificateDescendantBlockW2_09 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![5, -5, 5, -5, 5, -15, 5, 5, -5, 5;
     5, -5, -5, 5, 5, 5, -15, -5, 5, 5;
     -5, 5, 5, -5, 5, 5, -5, -15, 5, 5;
     -5, 5, -5, 5, 5, -5, 5, 5, -15, 5;
     -5, -5, 5, 5, -5, 5, 5, 5, 5, -15;
     18, -12, -12, -12, 18, 18, 18, -12, -12, -12;
     -12, 18, -12, -12, 18, -12, -12, 18, 18, -12;
     -12, -12, 18, -12, -12, 18, -12, 18, -12, 18;
     -12, -12, -12, 18, -12, -12, 18, -12, 18, 18;
     -9, -9, -9, -9, -9, -9, -9, -9, -9, -9]

/-- Exact integer inverse certificate for signed physical weight [-2, -3, 1]. -/
theorem certificateDescendantBlock2_09_inverse :
    certificateDescendantBlockA2_09 * certificateDescendantBlockW2_09 =
      (4320 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_09_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 9) := by decide

theorem certificateDescendantBlock2_09_row_weight (i : Fin 10) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 9 i) r) =
      certificateDescendantWeights2 9 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_09_column_weight (j : Fin 10) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 9)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 9 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_09_physical (i j : Fin 10) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 9 j))
      (certificateDescendantBlockRows2 9 i) = certificateDescendantBlockA2_09 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
