module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_21 : Matrix (Fin 11) (Fin 11) ℤ :=
  !![-24, -24, -24, -24, 24, 24, 24, 24, 24, 0, 24;
     24, 0, 0, 0, 0, -24, 0, 0, 0, 0, 24;
     0, 24, 0, 0, 0, 0, -24, 0, 0, 0, 24;
     0, 0, 24, 0, 0, 0, 0, -24, 0, 0, 24;
     0, 0, 0, 24, 0, 0, 0, 0, -24, 0, 24;
     0, 0, 0, 0, 24, 0, 0, 0, 0, -120, -120;
     0, 0, 0, 24, 0, 0, 0, 0, 24, 120, 96;
     0, 0, 24, 0, 0, 0, 0, 24, 0, 120, 96;
     0, 24, 0, 0, 0, 0, 24, 0, 0, 120, 96;
     24, 0, 0, 0, 0, 24, 0, 0, 0, 120, 96;
     -24, -24, -24, -24, 24, -24, -24, -24, -24, 120, 96]

def certificateDescendantBlockW2_21 : Matrix (Fin 11) (Fin 11) ℤ :=
  !![-5, 30, -5, -5, -5, 10, -5, -5, -5, 30, -5;
     -5, -5, 30, -5, -5, 10, -5, -5, 30, -5, -5;
     -5, -5, -5, 30, -5, 10, -5, 30, -5, -5, -5;
     -5, -5, -5, -5, 30, 10, 30, -5, -5, -5, -5;
     10, 10, 10, 10, 10, 50, 10, 10, 10, 10, 10;
     7, -28, 7, 7, 7, 0, -7, -7, -7, 28, -7;
     7, 7, -28, 7, 7, 0, -7, -7, 28, -7, -7;
     7, 7, 7, -28, 7, 0, -7, 28, -7, -7, -7;
     7, 7, 7, 7, -28, 0, 28, -7, -7, -7, -7;
     -10, -10, -10, -10, -10, 6, 4, 4, 4, 4, 4;
     12, 12, 12, 12, 12, -10, -2, -2, -2, -2, -2]

/-- Exact integer inverse certificate for signed physical weight [0, -4, 0]. -/
theorem certificateDescendantBlock2_21_inverse :
    certificateDescendantBlockA2_21 * certificateDescendantBlockW2_21 =
      (1680 : ℤ) • (1 : Matrix (Fin 11) (Fin 11) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_21_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 21) := by decide

theorem certificateDescendantBlock2_21_row_weight (i : Fin 11) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 21 i) r) =
      certificateDescendantWeights2 21 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_21_column_weight (j : Fin 11) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 21)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 21 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_21_physical (i j : Fin 11) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 21 j))
      (certificateDescendantBlockRows2 21 i) = certificateDescendantBlockA2_21 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
