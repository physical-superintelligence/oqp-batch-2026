module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_35 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, -1, -1;
     1, 0, -1;
     0, 1, -1]

def certificateDescendantBlockW1_35 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 2, -1;
     -1, -1, 2;
     -1, -1, -1]

/-- Exact integer inverse certificate for signed physical weight [3, -1, -2]. -/
theorem certificateDescendantBlock1_35_inverse :
    certificateDescendantBlockA1_35 * certificateDescendantBlockW1_35 =
      (3 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_35_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 35) := by decide

theorem certificateDescendantBlock1_35_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 35 i) r) =
      certificateDescendantWeights1 35 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_35_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 35)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 35 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_35_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 35 j))
      (certificateDescendantBlockRows1 35 i) = certificateDescendantBlockA1_35 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
