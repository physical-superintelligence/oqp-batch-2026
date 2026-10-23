module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_02 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-24, -24, 36;
     24, 0, 36;
     0, 24, 36]

def certificateDescendantBlockW1_02 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-3, 6, -3;
     -3, -3, 6;
     2, 2, 2]

/-- Exact integer inverse certificate for signed physical weight [-3, 2, 1]. -/
theorem certificateDescendantBlock1_02_inverse :
    certificateDescendantBlockA1_02 * certificateDescendantBlockW1_02 =
      (216 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_02_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 2) := by decide

theorem certificateDescendantBlock1_02_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 2 i) r) =
      certificateDescendantWeights1 2 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_02_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 2)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 2 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_02_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 2 j))
      (certificateDescendantBlockRows1 2 i) = certificateDescendantBlockA1_02 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
