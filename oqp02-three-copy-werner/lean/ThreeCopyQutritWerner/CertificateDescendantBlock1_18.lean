module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_18 : Matrix (Fin 93) (Fin 93) ℤ :=
  certificate_matrix% "verification/matrix-literals/b5ee7ed4ced8d729964f69773e81bbcd74ef5819f64e09c02c2982fb29e1d323.xz" "f7c804147bcd3bfd91c6ddeb47999141ff8ad53257a635b96aa314e850696dae"

def certificateDescendantBlockW1_18 : Matrix (Fin 93) (Fin 93) ℤ :=
  certificate_matrix% "verification/matrix-literals/b70da9d53cdc677346bfa0eaa7200f68703090a90c87275a0eff0e72a4840c2a.xz" "5a06510f37f49abff295c8189267ecf48bd0d6a70af3cae2660d2e330f9690aa"

/-- Exact integer inverse certificate for signed physical weight [0, 0, 0]. -/
theorem certificateDescendantBlock1_18_inverse :
    certificateDescendantBlockA1_18 * certificateDescendantBlockW1_18 =
      (15120 : ℤ) • (1 : Matrix (Fin 93) (Fin 93) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_18_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 18) := by decide

theorem certificateDescendantBlock1_18_row_weight (i : Fin 93) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 18 i) r) =
      certificateDescendantWeights1 18 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_18_column_weight (j : Fin 93) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 18)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 18 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_18_physical (i j : Fin 93) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 18 j))
      (certificateDescendantBlockRows1 18 i) = certificateDescendantBlockA1_18 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
