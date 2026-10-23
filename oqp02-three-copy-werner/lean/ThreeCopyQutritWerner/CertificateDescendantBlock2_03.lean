module

public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_03 : Matrix (Fin 11) (Fin 11) ℤ :=
  !![0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 120;
     0, 0, 0, 24, 0, 0, 0, 0, -12, -24, -744;
     0, 0, 24, 0, 0, 0, 0, -12, 0, -24, -744;
     0, 24, 0, 0, 0, 0, -12, 0, 0, -24, -744;
     24, 0, 0, 0, 0, -12, 0, 0, 0, -24, -744;
     -24, -24, -24, -24, 24, 12, 12, 12, 12, -24, -744;
     0, 0, 0, 24, 0, 0, 0, 0, 12, 24, 624;
     0, 0, 24, 0, 0, 0, 0, 12, 0, 24, 624;
     0, 24, 0, 0, 0, 0, 12, 0, 0, 24, 624;
     24, 0, 0, 0, 0, 12, 0, 0, 0, 24, 624;
     -24, -24, -24, -24, 24, -12, -12, -12, -12, 24, 624]

def certificateDescendantBlockW2_03 : Matrix (Fin 11) (Fin 11) ℤ :=
  !![10, -5, -5, -5, 30, -5, -5, -5, -5, 30, -5;
     10, -5, -5, 30, -5, -5, -5, -5, 30, -5, -5;
     10, -5, 30, -5, -5, -5, -5, 30, -5, -5, -5;
     10, 30, -5, -5, -5, -5, 30, -5, -5, -5, -5;
     50, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10;
     0, 14, 14, 14, -56, 14, -14, -14, -14, 56, -14;
     0, 14, 14, -56, 14, 14, -14, -14, 56, -14, -14;
     0, 14, -56, 14, 14, 14, -14, 56, -14, -14, -14;
     0, -56, 14, 14, 14, 14, 56, -14, -14, -14, -14;
     -114, 50, 50, 50, 50, 50, 64, 64, 64, 64, 64;
     4, -2, -2, -2, -2, -2, -2, -2, -2, -2, -2]

/-- Exact integer inverse certificate for signed physical weight [-4, 0, 0]. -/
theorem certificateDescendantBlock2_03_inverse :
    certificateDescendantBlockA2_03 * certificateDescendantBlockW2_03 =
      (1680 : ℤ) • (1 : Matrix (Fin 11) (Fin 11) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock2_03_rows_injective :
    Function.Injective (certificateDescendantBlockRows2 3) := by decide

theorem certificateDescendantBlock2_03_row_weight (i : Fin 11) :
    (fun r => certificateLocalWeight {0} (certificateDescendantBlockRows2 3 i) r) =
      certificateDescendantWeights2 3 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock2_03_column_weight (j : Fin 11) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0} a.1 r) =
      certificateDescendantWeights2 3)
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 3 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock2_03_physical (i j : Fin 11) :
    certificateSparseVector
      (certificateDescendantColumns2 (certificateDescendantBlockColumns2 3 j))
      (certificateDescendantBlockRows2 3 i) = certificateDescendantBlockA2_03 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
