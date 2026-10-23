module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_20 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![-720]

def certificateDescendantBlockW2_20 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![-1]

/-- Exact integer inverse certificate for signed physical weight [0, -5, 1]. -/
theorem certificateDescendantBlock2_20_inverse :
    certificateDescendantBlockA2_20 * certificateDescendantBlockW2_20 =
      (720 : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_20_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 20) := by decide

theorem certificateDescendantBlock2_20_row_weight (i : Fin 1) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 20 i) r) =
      certificateDescendantWeights2 20 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_20_column_weight (j : Fin 1) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 20)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 20 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_20_physical (i j : Fin 1) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 20 j))
      (certificateDescendantBlockRows2 20 i) = certificateDescendantBlockA2_20 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
