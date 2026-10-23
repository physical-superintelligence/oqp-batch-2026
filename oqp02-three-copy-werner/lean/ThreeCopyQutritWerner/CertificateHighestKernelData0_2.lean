module

public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel0_2Weight : Fin 3 → ℤ := ![0, 0, -4]

def certificateHighestKernel0_2Rows : Fin 11 → CertificateLocalWord :=
  ![![0, 2, 2, 2, 2, 0],
    ![1, 2, 2, 2, 2, 1],
    ![2, 0, 2, 2, 2, 0],
    ![2, 1, 2, 2, 2, 1],
    ![2, 2, 0, 2, 2, 0],
    ![2, 2, 1, 2, 2, 1],
    ![2, 2, 2, 0, 2, 0],
    ![2, 2, 2, 1, 2, 1],
    ![2, 2, 2, 2, 0, 0],
    ![2, 2, 2, 2, 1, 1],
    ![2, 2, 2, 2, 2, 2]]

def certificateHighestKernel0_2Pivots : Fin 5 → Fin 11 := ![4,
    6,
    8,
    0,
    10]

def certificateHighestKernel0_2Tests : Fin 6 → Fin 2 × CertificateLocalWord :=
  ![(0, ![1, 2, 2, 2, 2, 0]),
    (0, ![2, 1, 2, 2, 2, 0]),
    (0, ![2, 2, 1, 2, 2, 0]),
    (0, ![2, 2, 2, 1, 2, 0]),
    (0, ![2, 2, 2, 2, 1, 0]),
    (1, ![2, 2, 2, 2, 2, 1])]

def certificateHighestKernel0_2U : Matrix (Fin 11) (Fin 5) ℤ :=
  !![0, 0, 0, 1, 0;
    0, 0, 0, 1, 0;
    -1, -1, -1, -1, 1;
    -1, -1, -1, -1, 1;
    1, 0, 0, 0, 0;
    1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 0, 1]

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel0_2P : Matrix (Fin 5) (Fin 11) ℤ :=
  fun i j => if certificateHighestKernel0_2Pivots i = j then 1 else 0

def certificateHighestKernel0_2R : Matrix (Fin 6) (Fin 11) ℤ :=
  !![-1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0;
    0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 1]

def certificateHighestKernel0_2W : Matrix (Fin 11) (Fin 6) ℤ :=
  !![0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0;
    -1, -1, -1, -1, -1, -1;
    -1, 0, -1, -1, -1, -1;
    0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0]

def certificateHighestKernel0_2denominator : ℤ := 1

end ThreeCopyQutritWerner
