module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_12 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/23bea698e0d8a30f8ff3c0edaafe04a5cf70a379989318fd2affa6c68972bc37.xz" "1a224798b7b00f2621c701a52066593ceb137b24ef34b766f11a6c668ea7fc96"

def certificateDescendantBlockW1_12 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/89d9479f5b8860bf1b576a011714960f9c3580f1bf04333ded73dc68c7e6ab99.xz" "af2bd810a19c8c9a05f6a408353a8dac07e2e64acb66545acf245687362d8b63"

/-- Exact integer inverse certificate for signed physical weight [-1, 1, 0]. -/
theorem certificateDescendantBlock1_12_inverse :
    certificateDescendantBlockA1_12 * certificateDescendantBlockW1_12 =
      (90720 : ℤ) • (1 : Matrix (Fin 60) (Fin 60) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_12_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 12) := by decide

theorem certificateDescendantBlock1_12_row_weight (i : Fin 60) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 12 i) r) =
      certificateDescendantWeights1 12 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_12_column_weight (j : Fin 60) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 12)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 12 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_12_physical (i j : Fin 60) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 12 j))
      (certificateDescendantBlockRows1 12 i) = certificateDescendantBlockA1_12 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
