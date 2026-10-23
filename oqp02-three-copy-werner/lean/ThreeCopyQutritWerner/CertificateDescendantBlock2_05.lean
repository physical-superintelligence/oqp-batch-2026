module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_05 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![0, 0, 0, 0, 36, 0, 0, 24, 24, 36;
     0, 0, 0, 36, 0, 0, 24, 0, 24, 36;
     0, 0, 36, 0, 0, 0, 24, 24, 0, 36;
     0, 36, 0, 0, 0, 24, 0, 0, 24, 36;
     36, 0, 0, 0, 0, 24, 0, 24, 0, 36;
     -36, -36, -36, -36, -36, 24, 24, 0, 0, 36;
     0, -36, 0, -36, -36, -24, -24, -24, 0, 36;
     -36, 0, -36, 0, -36, -24, -24, 0, -24, 36;
     36, 36, 0, 0, 36, -24, 0, -24, -24, 36;
     0, 0, 36, 36, 36, 0, -24, -24, -24, 36]

def certificateDescendantBlockW2_05 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![-5, 5, -5, -5, 15, -5, 5, -5, 5, -5;
     -5, -5, 5, 15, -5, -5, -5, 5, 5, -5;
     -5, -5, 15, 5, -5, -5, 5, -5, -5, 5;
     -5, 15, -5, -5, 5, -5, -5, 5, -5, 5;
     15, -5, -5, -5, -5, 5, -5, -5, 5, 5;
     -6, -6, -6, 9, 9, 9, -6, -6, -6, 9;
     -6, 9, 9, -6, -6, 9, -6, -6, 9, -6;
     9, -6, 9, -6, 9, -6, -6, 9, -6, -6;
     9, 9, -6, 9, -6, -6, 9, -6, -6, -6;
     3, 3, 3, 3, 3, 3, 3, 3, 3, 3]

/-- Exact integer inverse certificate for signed physical weight [-3, -2, 1]. -/
theorem certificateDescendantBlock2_05_inverse :
    certificateDescendantBlockA2_05 * certificateDescendantBlockW2_05 =
      (1080 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_05_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 5) := by decide

theorem certificateDescendantBlock2_05_row_weight (i : Fin 10) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 5 i) r) =
      certificateDescendantWeights2 5 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_05_column_weight (j : Fin 10) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 5)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 5 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_05_physical (i j : Fin 10) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 5 j))
      (certificateDescendantBlockRows2 5 i) = certificateDescendantBlockA2_05 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
