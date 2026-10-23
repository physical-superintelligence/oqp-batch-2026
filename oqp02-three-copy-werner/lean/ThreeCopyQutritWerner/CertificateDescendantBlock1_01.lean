module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_01 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, -24, 72;
     -24, 0, 72;
     24, 24, 72]

def certificateDescendantBlockW1_01 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![3, -6, 3;
     -6, 3, 3;
     1, 1, 1]

/-- Exact integer inverse certificate for signed physical weight [-3, 1, 2]. -/
theorem certificateDescendantBlock1_01_inverse :
    certificateDescendantBlockA1_01 * certificateDescendantBlockW1_01 =
      (216 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_01_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 1) := by decide

theorem certificateDescendantBlock1_01_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 1 i) r) =
      certificateDescendantWeights1 1 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_01_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 1)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 1 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_01_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 1 j))
      (certificateDescendantBlockRows1 1 i) = certificateDescendantBlockA1_01 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
