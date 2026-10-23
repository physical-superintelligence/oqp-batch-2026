module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_28 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 0, 0, 6, 24;
     0, 0, 6, 0, 24;
     0, 6, 0, 0, 24;
     6, 0, 0, 0, 24;
     -6, -6, -6, -6, 24]

def certificateDescendantBlockW2_28 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-4, -4, -4, 16, -4;
     -4, -4, 16, -4, -4;
     -4, 16, -4, -4, -4;
     16, -4, -4, -4, -4;
     1, 1, 1, 1, 1]

/-- Exact integer inverse certificate for signed physical weight [1, -4, -1]. -/
theorem certificateDescendantBlock2_28_inverse :
    certificateDescendantBlockA2_28 * certificateDescendantBlockW2_28 =
      (120 : ℤ) • (1 : Matrix (Fin 5) (Fin 5) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_28_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 28) := by decide

theorem certificateDescendantBlock2_28_row_weight (i : Fin 5) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 28 i) r) =
      certificateDescendantWeights2 28 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_28_column_weight (j : Fin 5) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 28)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 28 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_28_physical (i j : Fin 5) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 28 j))
      (certificateDescendantBlockRows2 28 i) = certificateDescendantBlockA2_28 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
