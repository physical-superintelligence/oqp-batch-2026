module

public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel1_3Weight : Fin 3 → ℤ := ![2, 0, -2]

def certificateHighestKernel1_3Rows : Fin 15 → CertificateLocalWord :=
  ![![0, 0, 0, 0, 2, 2],
    ![0, 0, 0, 2, 0, 2],
    ![0, 0, 0, 2, 2, 0],
    ![0, 0, 1, 1, 2, 2],
    ![0, 0, 1, 2, 1, 2],
    ![0, 0, 1, 2, 2, 1],
    ![0, 0, 2, 2, 2, 2],
    ![0, 1, 0, 1, 2, 2],
    ![0, 1, 0, 2, 1, 2],
    ![0, 1, 0, 2, 2, 1],
    ![0, 2, 0, 2, 2, 2],
    ![1, 0, 0, 1, 2, 2],
    ![1, 0, 0, 2, 1, 2],
    ![1, 0, 0, 2, 2, 1],
    ![2, 0, 0, 2, 2, 2]]

def certificateHighestKernel1_3Pivots : Fin 9 → Fin 15 := ![4,
    5,
    6,
    8,
    9,
    10,
    12,
    13,
    14]

def certificateHighestKernel1_3Tests : Fin 6 → Fin 2 × CertificateLocalWord :=
  ![(0, ![0, 0, 0, 1, 2, 2]),
    (0, ![0, 0, 0, 2, 1, 2]),
    (0, ![0, 0, 0, 2, 2, 1]),
    (1, ![0, 0, 1, 2, 2, 2]),
    (1, ![0, 1, 0, 2, 2, 2]),
    (1, ![1, 0, 0, 2, 2, 2])]

def certificateHighestKernel1_3U : Matrix (Fin 15) (Fin 9) ℤ :=
  !![-1, -1, 1, -1, -1, 1, -1, -1, 1;
    1, 0, 0, 1, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 1, 0;
    -1, -1, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, -1, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, -1, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel1_3P : Matrix (Fin 9) (Fin 15) ℤ :=
  fun i j => if certificateHighestKernel1_3Pivots i = j then 1 else 0

def certificateHighestKernel1_3R : Matrix (Fin 6) (Fin 15) ℤ :=
  !![-1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0;
    0, 0, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, -1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, 1]

def certificateHighestKernel1_3W : Matrix (Fin 15) (Fin 6) ℤ :=
  !![-1, 0, 0, -1, -1, -1;
    0, -1, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

def certificateHighestKernel1_3denominator : ℤ := 1

end ThreeCopyQutritWerner
