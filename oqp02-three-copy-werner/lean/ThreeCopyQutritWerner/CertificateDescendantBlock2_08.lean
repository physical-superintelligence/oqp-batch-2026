module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_08 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, 0, 6, 0, 0, 4, 4, 6;
     0, 0, 0, 6, 0, 0, 4, 0, 4, 6;
     0, 0, 6, 0, 0, 0, 4, 4, 0, 6;
     0, 6, 0, 0, 0, 4, 0, 0, 4, 6;
     6, 0, 0, 0, 0, 4, 0, 4, 0, 6;
     -6, -6, -6, -6, -6, 4, 4, 0, 0, 6;
     0, -6, 0, -6, -6, -4, -4, -4, 0, 6;
     -6, 0, -6, 0, -6, -4, -4, 0, -4, 6;
     6, 6, 0, 0, 6, -4, 0, -4, -4, 6;
     0, 0, 6, 6, 6, 0, -4, -4, -4, 6]

def certificateDescendantBlockW2_08 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-5, 5, -5, -5, 15, -5, 5, -5, 5, -5;
     -5, -5, 5, 15, -5, -5, -5, 5, 5, -5;
     -5, -5, 15, 5, -5, -5, 5, -5, -5, 5;
     -5, 15, -5, -5, 5, -5, -5, 5, -5, 5;
     15, -5, -5, -5, -5, 5, -5, -5, 5, 5;
     -6, -6, -6, 9, 9, 9, -6, -6, -6, 9;
     -6, 9, 9, -6, -6, 9, -6, -6, 9, -6;
     9, -6, 9, -6, 9, -6, -6, 9, -6, -6;
     9, 9, -6, 9, -6, -6, 9, -6, -6, -6;
     3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

/-- Exact integer inverse certificate for signed physical weight [-3, 1, -2]. -/
theorem certificateDescendantBlock2_08_inverse :
    certificateDescendantBlockA2_08 * certificateDescendantBlockW2_08 =
      (180 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_08_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 8) := by decide

theorem certificateDescendantBlock2_08_row_weight (i : Fin 10) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 8 i) r) =
      certificateDescendantWeights2 8 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_08_column_weight (j : Fin 10) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 8)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 8 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_08_physical (i j : Fin 10) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 8 j))
      (certificateDescendantBlockRows2 8 i) = certificateDescendantBlockA2_08 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
