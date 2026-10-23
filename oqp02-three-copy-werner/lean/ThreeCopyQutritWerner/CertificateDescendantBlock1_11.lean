module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_11 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/1b67daafde43ee2a5eec7815448e67498bfaf974ad32e70a2e196b5b575ae653.xz" "495b562154127f8b828f0f1857eb1d7dab3cfe4abb14e1616e57c34076458183"

def certificateDescendantBlockW1_11 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/9ee0c47db6edb584621de65531ecc993924f319620159ba8150c09c6117530e0.xz" "a35ad08574786f16eff0b3f9376106e01645792e41724acf8d6fa0c405ae5b77"

/-- Exact integer inverse certificate for signed physical weight [-1, 0, 1]. -/
theorem certificateDescendantBlock1_11_inverse :
    certificateDescendantBlockA1_11 * certificateDescendantBlockW1_11 =
      (90720 : ℤ) • (1 : Matrix (Fin 60) (Fin 60) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_11_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 11) := by decide

theorem certificateDescendantBlock1_11_row_weight (i : Fin 60) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 11 i) r) =
      certificateDescendantWeights1 11 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_11_column_weight (j : Fin 60) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 11)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 11 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_11_physical (i j : Fin 60) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 11 j))
      (certificateDescendantBlockRows1 11 i) = certificateDescendantBlockA1_11 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
