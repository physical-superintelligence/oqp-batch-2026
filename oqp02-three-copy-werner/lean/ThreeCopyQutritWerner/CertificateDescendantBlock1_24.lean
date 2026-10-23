module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_24 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/30afe523c4f473e58bd7dfd4e3030e63c656c4c0025447fbcc8262f9023065f6.xz" "f221af02f23447fbb1e3209924413d101bb6a26d791b4d63f7b720c97f70c9e0"

def certificateDescendantBlockW1_24 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/6e4fbc330ae6ac28c3130c214f9e159e617783cf96e431c2075d99cfcf64f64d.xz" "2a111f718e6b718df2f523c2d325ceee24a7885ae30abc622c8114579197dc91"

/-- Exact integer inverse certificate for signed physical weight [1, -1, 0]. -/
theorem certificateDescendantBlock1_24_inverse :
    certificateDescendantBlockA1_24 * certificateDescendantBlockW1_24 =
      (15120 : ℤ) • (1 : Matrix (Fin 60) (Fin 60) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_24_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 24) := by decide

theorem certificateDescendantBlock1_24_row_weight (i : Fin 60) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 24 i) r) =
      certificateDescendantWeights1 24 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_24_column_weight (j : Fin 60) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 24)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 24 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_24_physical (i j : Fin 60) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 24 j))
      (certificateDescendantBlockRows1 24 i) = certificateDescendantBlockA1_24 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
