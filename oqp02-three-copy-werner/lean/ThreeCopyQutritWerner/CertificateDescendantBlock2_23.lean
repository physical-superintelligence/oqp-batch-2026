module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_23 : Matrix (Fin 50) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/c68f914fbb037679cfd151e1450f143a0fcaca956084ae11af81561a3c632b04.xz" "a25b3379f905692499e0fcc8eeef0b8a610eda783560141a8ea381c14bc27f21"

def certificateDescendantBlockW2_23 : Matrix (Fin 50) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/77ec11290164bfafe926954dbddb715812175091e55f23cd696ae415748606c1.xz" "a2517547a618d6f102a23a0d3ea6b8b67a32095effc072e5f77d12d7429c8f93"

/-- Exact integer inverse certificate for signed physical weight [0, -2, -2]. -/
theorem certificateDescendantBlock2_23_inverse :
    certificateDescendantBlockA2_23 * certificateDescendantBlockW2_23 =
      (2520 : ℤ) • (1 : Matrix (Fin 50) (Fin 50) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_23_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 23) := by decide

theorem certificateDescendantBlock2_23_row_weight (i : Fin 50) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 23 i) r) =
      certificateDescendantWeights2 23 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_23_column_weight (j : Fin 50) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 23)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 23 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_23_physical (i j : Fin 50) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 23 j))
      (certificateDescendantBlockRows2 23 i) = certificateDescendantBlockA2_23 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
