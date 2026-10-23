module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_17 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/5eef6cb0cd50b4b8c615e7aefc3d82f66719bba535c0c9baf41f9f3b09b4be9a.xz" "7f95b132789af042420a13f9f4674e3fccb34dbf2e2e9e884ee3e47fceac15c7"

def certificateDescendantBlockW1_17 : Matrix (Fin 60) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/1e70913ec65802ee935618e95b43cd9c900b8e32ae97b5e8d530e7762b7de12b.xz" "f79137cc7adf65053d71e696d1a417b9c37c418fdaf923c5b416ca56ff6cb0bd"

/-- Exact integer inverse certificate for signed physical weight [0, -1, 1]. -/
theorem certificateDescendantBlock1_17_inverse :
    certificateDescendantBlockA1_17 * certificateDescendantBlockW1_17 =
      (30240 : ℤ) • (1 : Matrix (Fin 60) (Fin 60) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_17_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 17) := by decide

theorem certificateDescendantBlock1_17_row_weight (i : Fin 60) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 17 i) r) =
      certificateDescendantWeights1 17 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_17_column_weight (j : Fin 60) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 17)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 17 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_17_physical (i j : Fin 60) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 17 j))
      (certificateDescendantBlockRows1 17 i) = certificateDescendantBlockA1_17 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
