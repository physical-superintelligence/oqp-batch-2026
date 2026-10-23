module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_14 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![240, 240, 240, 240, 120;
     -240, 0, 0, 0, 120;
     0, -240, 0, 0, 120;
     0, 0, -240, 0, 120;
     0, 0, 0, -240, 120]

def certificateDescendantBlockW2_14 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, -4, 1, 1, 1;
     1, 1, -4, 1, 1;
     1, 1, 1, -4, 1;
     1, 1, 1, 1, -4;
     2, 2, 2, 2, 2]

/-- Exact integer inverse certificate for signed physical weight [-1, -4, 1]. -/
theorem certificateDescendantBlock2_14_inverse :
    certificateDescendantBlockA2_14 * certificateDescendantBlockW2_14 =
      (1200 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_14_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 14) := by decide

theorem certificateDescendantBlock2_14_row_weight (i : Fin 5) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 14 i) r) =
      certificateDescendantWeights2 14 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_14_column_weight (j : Fin 5) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 14)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 14 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_14_physical (i j : Fin 5) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 14 j))
      (certificateDescendantBlockRows2 14 i) = certificateDescendantBlockA2_14 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
