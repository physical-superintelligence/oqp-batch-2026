module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_04 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 0, 0, 12, 24;
     0, 0, 12, 0, 24;
     0, 12, 0, 0, 24;
     12, 0, 0, 0, 24;
     -12, -12, -12, -12, 24]

def certificateDescendantBlockW2_04 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-2, -2, -2, 8, -2;
     -2, -2, 8, -2, -2;
     -2, 8, -2, -2, -2;
     8, -2, -2, -2, -2;
     1, 1, 1, 1, 1]

/-- Exact integer inverse certificate for signed physical weight [-4, 1, -1]. -/
theorem certificateDescendantBlock2_04_inverse :
    certificateDescendantBlockA2_04 * certificateDescendantBlockW2_04 =
      (120 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_04_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 4) := by decide

theorem certificateDescendantBlock2_04_row_weight (i : Fin 5) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 4 i) r) =
      certificateDescendantWeights2 4 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_04_column_weight (j : Fin 5) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 4)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 4 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_04_physical (i j : Fin 5) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 4 j))
      (certificateDescendantBlockRows2 4 i) = certificateDescendantBlockA2_04 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
