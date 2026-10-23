module

public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel0_3Weight : Fin 3 → ℤ := ![1, -2, -3]

def certificateHighestKernel0_3Rows : Fin 10 → CertificateLocalWord :=
  ![![1, 1, 2, 2, 2, 0],
    ![1, 2, 1, 2, 2, 0],
    ![1, 2, 2, 1, 2, 0],
    ![1, 2, 2, 2, 1, 0],
    ![2, 1, 1, 2, 2, 0],
    ![2, 1, 2, 1, 2, 0],
    ![2, 1, 2, 2, 1, 0],
    ![2, 2, 1, 1, 2, 0],
    ![2, 2, 1, 2, 1, 0],
    ![2, 2, 2, 1, 1, 0]]

def certificateHighestKernel0_3Pivots : Fin 5 → Fin 10 := ![8,
    1,
    9,
    2,
    3]

def certificateHighestKernel0_3Tests : Fin 5 → Fin 2 × CertificateLocalWord :=
  ![(1, ![1, 2, 2, 2, 2, 0]),
    (1, ![2, 1, 2, 2, 2, 0]),
    (1, ![2, 2, 1, 2, 2, 0]),
    (1, ![2, 2, 2, 1, 2, 0]),
    (1, ![2, 2, 2, 2, 1, 0])]

def certificateHighestKernel0_3U : Matrix (Fin 10) (Fin 5) ℤ :=
  !![0, -1, 0, -1, -1;
    0, 1, 0, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1;
    0, 0, 1, 1, 1;
    1, 1, 0, 0, 1;
    -1, 0, -1, 0, -1;
    -1, -1, -1, -1, -1;
    1, 0, 0, 0, 0;
    0, 0, 1, 0, 0]

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel0_3P : Matrix (Fin 5) (Fin 10) ℤ :=
  fun i j => if certificateHighestKernel0_3Pivots i = j then 1 else 0

def certificateHighestKernel0_3R : Matrix (Fin 5) (Fin 10) ℤ :=
  !![-1, -1, -1, -1, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, -1, -1, -1, 0, 0, 0;
    0, -1, 0, 0, -1, 0, 0, -1, -1, 0;
    0, 0, -1, 0, 0, -1, 0, -1, 0, -1;
    0, 0, 0, -1, 0, 0, -1, 0, -1, -1]

def certificateHighestKernel0_3W : Matrix (Fin 10) (Fin 5) ℤ :=
  !![-2, 0, 0, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, 0;
    1, -1, -1, 1, 1;
    1, -1, 1, -1, 1;
    0, 0, 0, 0, -2;
    -1, 1, -1, -1, -1;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, 0]

def certificateHighestKernel0_3denominator : ℤ := 2

end ThreeCopyQutritWerner
