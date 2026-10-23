module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_06 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/0d95568bc208a92a17b118152628c9a7d4a9ac8bd541780383859534ed9d107d.xz" "9d2135d2befa2907955878d6824e51ffc777d03ac08e6cbaebc62a54992cd2ac"

def certificateDescendantBlockW2_06 : Matrix (Fin 35) (Fin 35) ℤ :=
  certificate_matrix% "verification/matrix-literals/05a24dc96f69dfe926699d821e8276f1e44d1710fa767e9af90767bccc192363.xz" "8aaf26630c92758db71fd1e143edef0637121602f865e1e47b1bea05705aadd4"

/-- Exact integer inverse certificate for signed physical weight [-3, -1, 0]. -/
theorem certificateDescendantBlock2_06_inverse :
    certificateDescendantBlockA2_06 * certificateDescendantBlockW2_06 =
      (15120 : ℤ) • (1 : Matrix (Fin 35) (Fin 35) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_06_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 6) := by decide

theorem certificateDescendantBlock2_06_row_weight (i : Fin 35) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 6 i) r) =
      certificateDescendantWeights2 6 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_06_column_weight (j : Fin 35) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 6)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 6 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_06_physical (i j : Fin 35) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 6 j))
      (certificateDescendantBlockRows2 6 i) = certificateDescendantBlockA2_06 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
