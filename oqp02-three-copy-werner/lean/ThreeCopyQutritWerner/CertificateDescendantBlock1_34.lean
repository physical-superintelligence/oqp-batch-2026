module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_34 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 2;
     1, 0, 2;
     -1, -1, 2]

def certificateDescendantBlockW1_34 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-2, 4, -2;
     4, -2, -2;
     1, 1, 1]

/-- Exact integer inverse certificate for signed physical weight [3, -2, -1]. -/
theorem certificateDescendantBlock1_34_inverse :
    certificateDescendantBlockA1_34 * certificateDescendantBlockW1_34 =
      (6 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_34_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 34) := by decide

theorem certificateDescendantBlock1_34_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 34 i) r) =
      certificateDescendantWeights1 34 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_34_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 34)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 34 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_34_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 34 j))
      (certificateDescendantBlockRows1 34 i) = certificateDescendantBlockA1_34 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
