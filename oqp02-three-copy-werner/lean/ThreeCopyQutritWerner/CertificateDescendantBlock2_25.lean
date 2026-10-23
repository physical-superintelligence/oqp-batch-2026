module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_25 : Matrix (Fin 11) (Fin 11) ℤ :=
  !![-1, -1, -1, -1, 1, 1, 1, 1, 1, 0, 1;
     1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1;
     0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 1;
     0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 1;
     -1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1;
     1, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1;
     0, 1, 0, 0, 0, 0, 1, 0, 0, -1, -1;
     0, 0, 1, 0, 0, 0, 0, 1, 0, -1, -1;
     0, 0, 0, 1, 0, 0, 0, 0, 1, -1, -1;
     0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]

def certificateDescendantBlockW2_25 : Matrix (Fin 11) (Fin 11) ℤ :=
  !![-5, 30, -5, -5, -5, -5, 30, -5, -5, -5, 10;
     -5, -5, 30, -5, -5, -5, -5, 30, -5, -5, 10;
     -5, -5, -5, 30, -5, -5, -5, -5, 30, -5, 10;
     -5, -5, -5, -5, 30, -5, -5, -5, -5, 30, 10;
     10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 50;
     7, -28, 7, 7, 7, -7, 28, -7, -7, -7, 0;
     7, 7, -28, 7, 7, -7, -7, 28, -7, -7, 0;
     7, 7, 7, -28, 7, -7, -7, -7, 28, -7, 0;
     7, 7, 7, 7, -28, -7, -7, -7, -7, 28, 0;
     -10, -10, -10, -10, -10, -10, -10, -10, -10, -10, 20;
     12, 12, 12, 12, 12, -2, -2, -2, -2, -2, -10]

/-- Exact integer inverse certificate for signed physical weight [0, 0, -4]. -/
theorem certificateDescendantBlock2_25_inverse :
    certificateDescendantBlockA2_25 * certificateDescendantBlockW2_25 =
      (70 : ℤ) • (1 : Matrix (Fin 11) (Fin 11) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_25_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 25) := by decide

theorem certificateDescendantBlock2_25_row_weight (i : Fin 11) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 25 i) r) =
      certificateDescendantWeights2 25 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_25_column_weight (j : Fin 11) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 25)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 25 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_25_physical (i j : Fin 11) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 25 j))
      (certificateDescendantBlockRows2 25 i) = certificateDescendantBlockA2_25 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
