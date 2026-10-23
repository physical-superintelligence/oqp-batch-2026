module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_18 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/c68306206ee116a589912e2941936c729cc9347bdddaec39bf14a40467578978.xz" "c4f4c38465e596ca0f92bfd40489f1fe833a079bc03ef7783489b53157fe81d3"

def certificateDescendantBlockW2_18 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/f1074c91d84b1e7687809ef53c94477e5c35e37195bf778582d0e04952894401.xz" "098c9dd01fe4b50c2a7f9086b7b855e3d9d76b5aaf45359a51aa27851bcf2520"

/-- Exact integer inverse certificate for signed physical weight [-1, 0, -3]. -/
theorem certificateDescendantBlock2_18_inverse :
    certificateDescendantBlockA2_18 * certificateDescendantBlockW2_18 =
      (2520 : ℤ) • (1 : Matrix (Fin 35) (Fin 35) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_18_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 18) := by decide

theorem certificateDescendantBlock2_18_row_weight (i : Fin 35) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 18 i) r) =
      certificateDescendantWeights2 18 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_18_column_weight (j : Fin 35) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 18)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 18 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_18_physical (i j : Fin 35) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 18 j))
      (certificateDescendantBlockRows2 18 i) = certificateDescendantBlockA2_18 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
