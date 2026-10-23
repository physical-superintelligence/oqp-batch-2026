module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_22 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/862a25bc03d9415149145fd573cbb1931f3204c3b215ac77b5ed3fc672b90bfa.xz" "a131311bc27706831bbf9854bff75233401ec1dc0da342419512c4b84dc6fc17"

def certificateDescendantBlockW2_22 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/a9e72c6f497436cafb9fa65a1e63a37e900d48d2d176a5bfd496331157c9669c.xz" "ecc7c014adfa85c1ba881eb658f3ea8e42649141c8820f7aed8360fbc1fbf426"

/-- Exact integer inverse certificate for signed physical weight [0, -3, -1]. -/
theorem certificateDescendantBlock2_22_inverse :
    certificateDescendantBlockA2_22 * certificateDescendantBlockW2_22 =
      (5040 : ℤ) • (1 : Matrix (Fin 35) (Fin 35) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_22_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 22) := by decide

theorem certificateDescendantBlock2_22_row_weight (i : Fin 35) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 22 i) r) =
      certificateDescendantWeights2 22 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_22_column_weight (j : Fin 35) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 22)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 22 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_22_physical (i j : Fin 35) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 22 j))
      (certificateDescendantBlockRows2 22 i) = certificateDescendantBlockA2_22 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
