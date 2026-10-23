module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_10 : Matrix (Fin 50) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/8bc1ddb3de2d9dfcaddbae248c7471ed2f385ee331531a697c86b78213de8520.xz" "4a2dfba9c105e9269a64dac49bc69acad79e7d21f7f090a8686bfa8d8177b5a9"

def certificateDescendantBlockW2_10 : Matrix (Fin 50) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/ee99a3048d37d60183ea9961d60152856321d56155fd79159824962e7ebccd6d.xz" "e3d62119191e5897dd2805282fe166840ec7a4c7297ad897fc641380df25548d"

/-- Exact integer inverse certificate for signed physical weight [-2, -2, 0]. -/
theorem certificateDescendantBlock2_10_inverse :
    certificateDescendantBlockA2_10 * certificateDescendantBlockW2_10 =
      (15120 : ℤ) • (1 : Matrix (Fin 50) (Fin 50) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_10_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 10) := by decide

theorem certificateDescendantBlock2_10_row_weight (i : Fin 50) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 10 i) r) =
      certificateDescendantWeights2 10 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_10_column_weight (j : Fin 50) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 10)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 10 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_10_physical (i j : Fin 50) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 10 j))
      (certificateDescendantBlockRows2 10 i) = certificateDescendantBlockA2_10 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
