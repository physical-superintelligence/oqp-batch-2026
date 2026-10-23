module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_07 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -6, 0, 12;
     0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -6, 0, 0, 12;
     0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 0, 12;
     0, 4, 0, 0, 4, 0, 0, 4, 0, 0, -24, 0, 0, -12, -84;
     4, 0, 0, 4, 0, 0, 4, 0, 0, -24, 0, 0, 0, -12, -84;
     -4, -4, 4, -4, -4, 4, -4, -4, 4, 24, 24, 0, 0, -12, -84;
     0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 24, -6, -6, 12, 72;
     4, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, -6, -6, 12, 72;
     -4, -4, 4, 0, 0, 0, 0, 0, 0, -24, -24, -6, -6, 12, 72;
     0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 24, 6, 0, 12, 72;
     0, 0, 0, 4, 0, 0, 0, 0, 0, 24, 0, 6, 0, 12, 72;
     0, 0, 0, -4, -4, 4, 0, 0, 0, -24, -24, 6, 0, 12, 72;
     0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 24, 0, 6, 12, 72;
     0, 0, 0, 0, 0, 0, 4, 0, 0, 24, 0, 0, 6, 12, 72;
     0, 0, 0, 0, 0, 0, -4, -4, 4, -24, -24, 0, 6, 12, 72]

def certificateDescendantBlockW1_07 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![-18, -18, 108, -18, 108, -18, -90, 288, -90, 36, -90, 36, 36, -90, 36;
     -18, -18, 108, 108, -18, -18, 288, -90, -90, -90, 36, 36, -90, 36, 36;
     -54, -54, 324, 72, 72, 72, 108, 108, 108, -18, -18, -18, -18, -18, -18;
     -18, 108, -18, -18, 108, -18, 36, -90, 36, -90, 288, -90, 36, -90, 36;
     -18, 108, -18, 108, -18, -18, -90, 36, 36, 288, -90, -90, -90, 36, 36;
     -54, 324, -54, 72, 72, 72, -18, -18, -18, 108, 108, 108, -18, -18, -18;
     108, -18, -18, -18, 108, -18, 36, -90, 36, 36, -90, 36, -90, 288, -90;
     108, -18, -18, 108, -18, -18, -90, 36, 36, -90, 36, 36, 288, -90, -90;
     324, -54, -54, 72, 72, 72, -18, -18, -18, -18, -18, -18, 108, 108, 108;
     0, 0, 0, 7, -14, 7, -7, 14, -7, -7, 14, -7, -7, 14, -7;
     0, 0, 0, -14, 7, 7, 14, -7, -7, 14, -7, -7, 14, -7, -7;
     28, -56, 28, 0, 0, 0, -28, -28, -28, 56, 56, 56, -28, -28, -28;
     -56, 28, 28, 0, 0, 0, -28, -28, -28, -28, -28, -28, 56, 56, 56;
     -200, -200, -200, 136, 136, 136, 64, 64, 64, 64, 64, 64, 64, 64, 64;
     32, 32, 32, -24, -24, -24, -8, -8, -8, -8, -8, -8, -8, -8, -8]

/-- Exact integer inverse certificate for signed physical weight [-2, 2, 0]. -/
theorem certificateDescendantBlock1_07_inverse :
    certificateDescendantBlockA1_07 * certificateDescendantBlockW1_07 =
      (2016 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_07_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 7) := by decide

theorem certificateDescendantBlock1_07_row_weight (i : Fin 15) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 7 i) r) =
      certificateDescendantWeights1 7 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_07_column_weight (j : Fin 15) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 7)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 7 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_07_physical (i j : Fin 15) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 7 j))
      (certificateDescendantBlockRows1 7 i) = certificateDescendantBlockA1_07 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
