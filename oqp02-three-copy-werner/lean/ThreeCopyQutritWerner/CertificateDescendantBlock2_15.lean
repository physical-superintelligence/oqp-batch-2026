module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_15 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/21b144b758c0f2f8f4ceaa5d73fbd1eb32310c63074b2f7c654e7fcfe8ecf275.xz" "e15721440c8e5aec42f4872c5285e4b9c204c2de454fdba9b78caf6efb862675"

def certificateDescendantBlockW2_15 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/155f1c0f02b526cae0df2278f3c6033383082a5e9b272f4d98d515a32c0d89e4.xz" "253c88e66ce368c01365493f7165e4d4dfe18a0fe2e60fa70290d305f2af0387"

/-- Exact integer inverse certificate for signed physical weight [-1, -3, 0]. -/
theorem certificateDescendantBlock2_15_inverse :
    certificateDescendantBlockA2_15 * certificateDescendantBlockW2_15 =
      (15120 : ℤ) • (1 : Matrix (Fin 35) (Fin 35) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_15_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 15) := by decide

theorem certificateDescendantBlock2_15_row_weight (i : Fin 35) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 15 i) r) =
      certificateDescendantWeights2 15 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_15_column_weight (j : Fin 35) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 15)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 15 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_15_physical (i j : Fin 35) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 15 j))
      (certificateDescendantBlockRows2 15 i) = certificateDescendantBlockA2_15 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
