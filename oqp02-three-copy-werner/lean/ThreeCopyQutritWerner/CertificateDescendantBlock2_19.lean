module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_19 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, 2, 2, 2, 1;
     -2, 0, 0, 0, 1;
     0, -2, 0, 0, 1;
     0, 0, -2, 0, 1;
     0, 0, 0, -2, 1]

def certificateDescendantBlockW2_19 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, -4, 1, 1, 1;
     1, 1, -4, 1, 1;
     1, 1, 1, -4, 1;
     1, 1, 1, 1, -4;
     2, 2, 2, 2, 2]

/-- Exact integer inverse certificate for signed physical weight [-1, 1, -4]. -/
theorem certificateDescendantBlock2_19_inverse :
    certificateDescendantBlockA2_19 * certificateDescendantBlockW2_19 =
      (10 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_19_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 19) := by decide

theorem certificateDescendantBlock2_19_row_weight (i : Fin 5) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 19 i) r) =
      certificateDescendantWeights2 19 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_19_column_weight (j : Fin 5) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 19)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 19 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_19_physical (i j : Fin 5) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 19 j))
      (certificateDescendantBlockRows2 19 i) = certificateDescendantBlockA2_19 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
