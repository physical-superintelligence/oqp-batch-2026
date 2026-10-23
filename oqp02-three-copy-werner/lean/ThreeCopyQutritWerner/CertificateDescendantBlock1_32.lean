module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_32 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, -1, 1;
     1, 0, 1;
     0, 1, 1]

def certificateDescendantBlockW1_32 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 2, -1;
     -1, -1, 2;
     1, 1, 1]

/-- Exact integer inverse certificate for signed physical weight [2, 1, -3]. -/
theorem certificateDescendantBlock1_32_inverse :
    certificateDescendantBlockA1_32 * certificateDescendantBlockW1_32 =
      (3 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_32_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 32) := by decide

theorem certificateDescendantBlock1_32_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 32 i) r) =
      certificateDescendantWeights1 32 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_32_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 32)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 32 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_32_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 32 j))
      (certificateDescendantBlockRows1 32 i) = certificateDescendantBlockA1_32 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
