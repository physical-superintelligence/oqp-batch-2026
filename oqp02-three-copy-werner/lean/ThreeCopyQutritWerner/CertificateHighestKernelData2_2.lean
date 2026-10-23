module

public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel2_2Weight : Fin 3 → ℤ := ![0, 0, -4]

def certificateHighestKernel2_2Rows : Fin 11 → CertificateLocalWord :=
  ![![0, 0, 2, 2, 2, 2],
    ![0, 2, 0, 2, 2, 2],
    ![0, 2, 2, 0, 2, 2],
    ![0, 2, 2, 2, 0, 2],
    ![0, 2, 2, 2, 2, 0],
    ![1, 1, 2, 2, 2, 2],
    ![1, 2, 1, 2, 2, 2],
    ![1, 2, 2, 1, 2, 2],
    ![1, 2, 2, 2, 1, 2],
    ![1, 2, 2, 2, 2, 1],
    ![2, 2, 2, 2, 2, 2]]

def certificateHighestKernel2_2Pivots : Fin 5 → Fin 11 := ![1,
    2,
    3,
    4,
    10]

def certificateHighestKernel2_2Tests : Fin 6 → Fin 2 × CertificateLocalWord :=
  ![(0, ![0, 1, 2, 2, 2, 2]),
    (0, ![0, 2, 1, 2, 2, 2]),
    (0, ![0, 2, 2, 1, 2, 2]),
    (0, ![0, 2, 2, 2, 1, 2]),
    (0, ![0, 2, 2, 2, 2, 1]),
    (1, ![1, 2, 2, 2, 2, 2])]

def certificateHighestKernel2_2U : Matrix (Fin 11) (Fin 5) ℤ :=
  !![-1, -1, -1, -1, 1;
    1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    -1, -1, -1, -1, 1;
    1, 0, 0, 0, 0;
    0, 1, 0, 0, 0;
    0, 0, 1, 0, 0;
    0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel2_2P : Matrix (Fin 5) (Fin 11) ℤ :=
  fun i j => if certificateHighestKernel2_2Pivots i = j then 1 else 0

def certificateHighestKernel2_2R : Matrix (Fin 6) (Fin 11) ℤ :=
  !![-1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, -1, -1, -1, -1, -1, 1]

def certificateHighestKernel2_2W : Matrix (Fin 11) (Fin 6) ℤ :=
  !![-1, -1, -1, -1, -1, -1;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, -1, -1, -1, -1, -1;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0]

def certificateHighestKernel2_2denominator : ℤ := 1

end ThreeCopyQutritWerner
