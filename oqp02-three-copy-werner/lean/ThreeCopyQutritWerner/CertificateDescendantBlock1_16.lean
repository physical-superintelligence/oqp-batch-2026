module

public import ThreeCopyQutritWerner.CertificateDescendantData1

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA1_16 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![0, 0, 0, 0, 0, 0, -48, -48, 48, 144, 144, 0, -24, 0, 48;
     0, 0, 0, 0, 0, 0, 48, 0, 0, -144, 0, 0, -24, 0, 48;
     0, 0, 0, 0, 0, 0, 0, 48, 0, 0, -144, 0, -24, 0, 48;
     0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 24, -720, -624;
     0, 0, 0, -48, -48, 48, 0, 0, 0, 144, 144, -24, 0, 0, 48;
     0, 0, 0, 48, 0, 0, 0, 0, 0, -144, 0, -24, 0, 0, 48;
     0, 0, 0, 0, 48, 0, 0, 0, 0, 0, -144, -24, 0, 0, 48;
     0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 24, 0, -720, -624;
     -48, -48, 48, 0, 0, 0, 0, 0, 0, 144, 144, 24, 24, 0, 48;
     48, 0, 0, 0, 0, 0, 0, 0, 0, -144, 0, 24, 24, 0, 48;
     0, 48, 0, 0, 0, 0, 0, 0, 0, 0, -144, 24, 24, 0, 48;
     0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, -24, -24, -720, -624;
     0, 48, 0, 0, 48, 0, 0, 48, 0, 0, 144, 0, 0, 720, 576;
     48, 0, 0, 48, 0, 0, 48, 0, 0, 144, 0, 0, 0, 720, 576;
     -48, -48, 48, -48, -48, 48, -48, -48, 48, -144, -144, 0, 0, 720, 576]

def certificateDescendantBlockW1_16 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![90, -225, 90, -45, 90, -225, 90, -45, -225, 720, -225, 270, -45, 270, -45;
     90, 90, -225, -45, 90, 90, -225, -45, -225, -225, 720, 270, 270, -45, -45;
     -45, -45, -45, -135, -45, -45, -45, -135, 270, 270, 270, 810, 180, 180, 180;
     90, -225, 90, -45, -225, 720, -225, 270, 90, -225, 90, -45, -45, 270, -45;
     90, 90, -225, -45, -225, -225, 720, 270, 90, 90, -225, -45, 270, -45, -45;
     -45, -45, -45, -135, 270, 270, 270, 810, -45, -45, -45, -135, 180, 180, 180;
     -225, 720, -225, 270, 90, -225, 90, -45, 90, -225, 90, -45, -45, 270, -45;
     -225, -225, 720, 270, 90, 90, -225, -45, 90, 90, -225, -45, 270, -45, -45;
     270, 270, 270, 810, -45, -45, -45, -135, -45, -45, -45, -135, 180, 180, 180;
     35, -70, 35, 0, 35, -70, 35, 0, 35, -70, 35, 0, -35, 70, -35;
     35, 35, -70, 0, 35, 35, -70, 0, 35, 35, -70, 0, 70, -35, -35;
     210, 210, 210, -210, -420, -420, -420, 420, 210, 210, 210, -210, 0, 0, 0;
     -420, -420, -420, 420, 210, 210, 210, -210, 210, 210, 210, -210, 0, 0, 0;
     -100, -100, -100, 36, -100, -100, -100, 36, -100, -100, -100, 36, 64, 64, 64;
     120, 120, 120, -60, 120, 120, 120, -60, 120, 120, 120, -60, -60, -60, -60]

/-- Exact integer inverse certificate for signed physical weight [0, -2, 2]. -/
theorem certificateDescendantBlock1_16_inverse :
    certificateDescendantBlockA1_16 * certificateDescendantBlockW1_16 =
      (60480 : ℤ) • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem certificateDescendantBlock1_16_rows_injective :
    Function.Injective (certificateDescendantBlockRows1 16) := by decide

theorem certificateDescendantBlock1_16_row_weight (i : Fin 15) :
    (fun r => certificateLocalWeight {0, 1, 2} (certificateDescendantBlockRows1 16 i) r) =
      certificateDescendantWeights1 16 := by
  fin_cases i <;> decide

theorem certificateDescendantBlock1_16_column_weight (j : Fin 15) :
    List.Forall (fun a => (fun r => certificateLocalWeight {0, 1, 2} a.1 r) =
      certificateDescendantWeights1 16)
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 16 j)) := by
  fin_cases j <;> decide

theorem certificateDescendantBlock1_16_physical (i j : Fin 15) :
    certificateSparseVector
      (certificateDescendantColumns1 (certificateDescendantBlockColumns1 16 j))
      (certificateDescendantBlockRows1 16 i) = certificateDescendantBlockA1_16 i j := by
  fin_cases i <;> fin_cases j <;> decide

end ThreeCopyQutritWerner
