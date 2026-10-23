module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_12 : Matrix (Fin 50) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/b8e01406b26c39d20e5c8baef7fa6e867426a55988b332c2888ad6ac6936c47d.xz" "7fdb121bdc84920883dcbdf5a926f0971297634c7d3cd20853d1762eb61d8627"

def certificateDescendantBlockW2_12 : Matrix (Fin 50) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/62822697a2994f04cd91d44e07e406e6f0d2216f594325d90e86f6a610c6261e.xz" "76c32d12042c81680742f925327d04fca35e59eb125fac6e3f892d894489067b"

/-- Exact integer inverse certificate for signed physical weight [-2, 0, -2]. -/
theorem certificateDescendantBlock2_12_inverse :
    certificateDescendantBlockA2_12 * certificateDescendantBlockW2_12 =
      (2520 : ℤ) • (1 : Matrix (Fin 50) (Fin 50) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_12_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 12) := by decide

theorem certificateDescendantBlock2_12_row_weight (i : Fin 50) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 12 i) r) =
      certificateDescendantWeights2 12 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_12_column_weight (j : Fin 50) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 12)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 12 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_12_physical (i j : Fin 50) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 12 j))
      (certificateDescendantBlockRows2 12 i) = certificateDescendantBlockA2_12 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
