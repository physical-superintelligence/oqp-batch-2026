module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_13 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 6, 6, 6, 0, 2, 2, 2, 2;
     6, 6, 0, 0, 6, 2, 0, 2, 2, 2;
     -6, 0, -6, 0, -6, 2, 2, 0, 2, 2;
     0, -6, 0, -6, -6, 2, 2, 2, 0, 2;
     -6, -6, -6, -6, -6, -2, -2, 0, 0, 2;
     6, 0, 0, 0, 0, -2, 0, -2, 0, 2;
     0, 6, 0, 0, 0, -2, 0, 0, -2, 2;
     0, 0, 6, 0, 0, 0, -2, -2, 0, 2;
     0, 0, 0, 6, 0, 0, -2, 0, -2, 2;
     0, 0, 0, 0, 6, 0, 0, -2, -2, 2]

def certificateDescendantBlockW2_13 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-5, 5, -5, 5, -5, 15, -5, -5, 5, -5;
     -5, 5, 5, -5, -5, -5, 15, 5, -5, -5;
     5, -5, -5, 5, -5, -5, 5, 15, -5, -5;
     5, -5, 5, -5, -5, 5, -5, -5, 15, -5;
     5, 5, -5, -5, 5, -5, -5, -5, -5, 15;
     -18, 12, 12, 12, -18, -18, -18, 12, 12, 12;
     12, -18, 12, 12, -18, 12, 12, -18, -18, 12;
     12, 12, -18, 12, 12, -18, 12, -18, 12, -18;
     12, 12, 12, -18, 12, 12, -18, 12, -18, -18;
     9, 9, 9, 9, 9, 9, 9, 9, 9, 9]

/-- Exact integer inverse certificate for signed physical weight [-2, 1, -3]. -/
theorem certificateDescendantBlock2_13_inverse :
    certificateDescendantBlockA2_13 * certificateDescendantBlockW2_13 =
      (180 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_13_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 13) := by decide

theorem certificateDescendantBlock2_13_row_weight (i : Fin 10) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 13 i) r) =
      certificateDescendantWeights2 13 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_13_column_weight (j : Fin 10) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 13)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 13 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_13_physical (i j : Fin 10) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 13 j))
      (certificateDescendantBlockRows2 13 i) = certificateDescendantBlockA2_13 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
