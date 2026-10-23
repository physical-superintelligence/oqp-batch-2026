module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_27 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![-120]

def certificateDescendantBlockW2_27 : Matrix (Fin 1) (Fin 1) ℤ :=
  !![-1]

/-- Exact integer inverse certificate for signed physical weight [1, -5, 0]. -/
theorem certificateDescendantBlock2_27_inverse :
    certificateDescendantBlockA2_27 * certificateDescendantBlockW2_27 =
      (120 : ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_27_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 27) := by decide

theorem certificateDescendantBlock2_27_row_weight (i : Fin 1) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 27 i) r) =
      certificateDescendantWeights2 27 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_27_column_weight (j : Fin 1) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 27)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 27 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_27_physical (i j : Fin 1) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 27 j))
      (certificateDescendantBlockRows2 27 i) = certificateDescendantBlockA2_27 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
