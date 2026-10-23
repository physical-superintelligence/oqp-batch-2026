module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_05 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, -12, 0, 24;
     0, 0, 0, 0, 0, 0, 0, 8, 0, 0, -144, 0, 12, -72, -456;
     0, 0, 0, 0, 0, 0, 8, 0, 0, -144, 0, 0, 12, -72, -456;
     0, 0, 0, 0, 0, 0, -8, -8, 8, 144, 144, 0, 12, -72, -456;
     0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, -12, 0, 0, 24;
     0, 0, 0, 0, 8, 0, 0, 0, 0, 0, -144, 12, 0, -72, -456;
     0, 0, 0, 8, 0, 0, 0, 0, 0, -144, 0, 12, 0, -72, -456;
     0, 0, 0, -8, -8, 8, 0, 0, 0, 144, 144, 12, 0, -72, -456;
     0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 0, 24;
     0, 8, 0, 0, 0, 0, 0, 0, 0, 0, -144, -12, -12, -72, -456;
     8, 0, 0, 0, 0, 0, 0, 0, 0, -144, 0, -12, -12, -72, -456;
     -8, -8, 8, 0, 0, 0, 0, 0, 0, 144, 144, -12, -12, -72, -456;
     0, 8, 0, 0, 8, 0, 0, 8, 0, 0, 144, 0, 0, 72, 432;
     8, 0, 0, 8, 0, 0, 8, 0, 0, 144, 0, 0, 0, 72, 432;
     -8, -8, 8, -8, -8, 8, -8, -8, 8, -144, -144, 0, 0, 72, 432]

def certificateDescendantBlockW1_05 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![-54, 108, -270, 108, -54, 108, -270, 108, 324, -270, 864, -270, -54, 324, -54;
     -54, -270, 108, 108, -54, -270, 108, 108, 324, 864, -270, -270, 324, -54, -54;
     -162, -54, -54, -54, -162, -54, -54, -54, 972, 324, 324, 324, 216, 216, 216;
     -54, 108, -270, 108, 324, -270, 864, -270, -54, 108, -270, 108, -54, 324, -54;
     -54, -270, 108, 108, 324, 864, -270, -270, -54, -270, 108, 108, 324, -54, -54;
     -162, -54, -54, -54, 972, 324, 324, 324, -162, -54, -54, -54, 216, 216, 216;
     324, -270, 864, -270, -54, 108, -270, 108, -54, 108, -270, 108, -54, 324, -54;
     324, 864, -270, -270, -54, -270, 108, 108, -54, -270, 108, 108, 324, -54, -54;
     972, 324, 324, 324, -162, -54, -54, -54, -162, -54, -54, -54, 216, 216, 216;
     0, 7, -14, 7, 0, 7, -14, 7, 0, 7, -14, 7, -7, 14, -7;
     0, -14, 7, 7, 0, -14, 7, 7, 0, -14, 7, 7, 14, -7, -7;
     84, -84, -84, -84, -168, 168, 168, 168, 84, -84, -84, -84, 0, 0, 0;
     -168, 168, 168, 168, 84, -84, -84, -84, 84, -84, -84, -84, 0, 0, 0;
     -600, 136, 136, 136, -600, 136, 136, 136, -600, 136, 136, 136, 464, 464, 464;
     96, -24, -24, -24, 96, -24, -24, -24, 96, -24, -24, -24, -72, -72, -72]

/-- Exact integer inverse certificate for signed physical weight [-2, 0, 2]. -/
theorem certificateDescendantBlock1_05_inverse :
    certificateDescendantBlockA1_05 * certificateDescendantBlockW1_05 =
      (12096 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_05_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 5) := by decide

theorem certificateDescendantBlock1_05_row_weight (i : Fin 15) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 5 i) r) =
      certificateDescendantWeights1 5 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_05_column_weight (j : Fin 15) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 5)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 5 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_05_physical (i j : Fin 15) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 5 j))
      (certificateDescendantBlockRows1 5 i) = certificateDescendantBlockA1_05 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
