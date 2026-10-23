module

public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel2_1Weight : Fin 3 → ℤ := ![1, -1, -4]

def certificateHighestKernel2_1Rows : Fin 5 → CertificateLocalWord :=
  ![![0, 1, 2, 2, 2, 2],
    ![0, 2, 1, 2, 2, 2],
    ![0, 2, 2, 1, 2, 2],
    ![0, 2, 2, 2, 1, 2],
    ![0, 2, 2, 2, 2, 1]]

def certificateHighestKernel2_1Pivots : Fin 4 → Fin 5 := ![1,
    2,
    3,
    4]

def certificateHighestKernel2_1Tests : Fin 1 → Fin 2 × CertificateLocalWord :=
  ![(1, ![0, 2, 2, 2, 2, 2])]

def certificateHighestKernel2_1U : Matrix (Fin 5) (Fin 4) ℤ :=
  !![-1, -1, -1, -1;
    1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, 1, 0;
    0, 0, 0, 1]

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel2_1P : Matrix (Fin 4) (Fin 5) ℤ :=
  fun i j => if certificateHighestKernel2_1Pivots i = j then 1 else 0

def certificateHighestKernel2_1R : Matrix (Fin 1) (Fin 5) ℤ :=
  !![-1, -1, -1, -1, -1]

def certificateHighestKernel2_1W : Matrix (Fin 5) (Fin 1) ℤ :=
  !![-1;
    0;
    0;
    0;
    0]

def certificateHighestKernel2_1denominator : ℤ := 1

end ThreeCopyQutritWerner
