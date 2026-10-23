module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_08 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 24, 12;
     24, 0, 12;
     -24, -24, 12]

def certificateDescendantBlockW1_08 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 2, -1;
     2, -1, -1;
     2, 2, 2]

/-- Exact integer inverse certificate for signed physical weight [-2, 3, -1]. -/
theorem certificateDescendantBlock1_08_inverse :
    certificateDescendantBlockA1_08 * certificateDescendantBlockW1_08 =
      (72 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_08_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 8) := by decide

theorem certificateDescendantBlock1_08_row_weight (i : Fin 3) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 8 i) r) =
      certificateDescendantWeights1 8 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_08_column_weight (j : Fin 3) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 8)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 8 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_08_physical (i j : Fin 3) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 8 j))
      (certificateDescendantBlockRows1 8 i) = certificateDescendantBlockA1_08 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
