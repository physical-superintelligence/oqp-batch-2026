module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_25 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/dea4c976a281658f7bf66878b0fc50a3baeaee67e924a81fda3a751812dea76d.xz" "7d8fd5713b62ee63a43241f37ee277be5bc34b77da1ab998da3c8f8c5cb8416b"

def certificateDescendantBlockW1_25 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/fed1b969e111bdfd345ae500f8d306e2fef434600b1b221758b4da8a1930c1f9.xz" "f0442a60ced4cfe8ff1d26ca672a6024ebea5a9dcdc6584b07f25cbbd7a0beb7"

/-- Exact integer inverse certificate for signed physical weight [1, 0, -1]. -/
theorem certificateDescendantBlock1_25_inverse :
    certificateDescendantBlockA1_25 * certificateDescendantBlockW1_25 =
      (7560 : ℤ) • (1 : Matrix (Fin 60) (Fin 60) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_25_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 25) := by decide

theorem certificateDescendantBlock1_25_row_weight (i : Fin 60) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 25 i) r) =
      certificateDescendantWeights1 25 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_25_column_weight (j : Fin 60) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 25)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 25 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_25_physical (i j : Fin 60) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 25 j))
      (certificateDescendantBlockRows1 25 i) = certificateDescendantBlockA1_25 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
