module

public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel1_1Weight : Fin 3 → ℤ := ![3, -1, -2]

def certificateHighestKernel1_1Rows : Fin 3 → CertificateLocalWord :=
  ![![0, 0, 0, 1, 2, 2],
    ![0, 0, 0, 2, 1, 2],
    ![0, 0, 0, 2, 2, 1]]

def certificateHighestKernel1_1Pivots : Fin 2 → Fin 3 := ![1,
    2]

def certificateHighestKernel1_1Tests : Fin 1 → Fin 2 × CertificateLocalWord :=
  ![(1, ![0, 0, 0, 2, 2, 2])]

def certificateHighestKernel1_1U : Matrix (Fin 3) (Fin 2) ℤ :=
  !![-1, -1;
    1, 0;
    0, 1]

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel1_1P : Matrix (Fin 2) (Fin 3) ℤ :=
  fun i j => if certificateHighestKernel1_1Pivots i = j then 1 else 0

def certificateHighestKernel1_1R : Matrix (Fin 1) (Fin 3) ℤ :=
  !![-1, -1, -1]

def certificateHighestKernel1_1W : Matrix (Fin 3) (Fin 1) ℤ :=
  !![-1;
    0;
    0]

def certificateHighestKernel1_1denominator : ℤ := 1

end ThreeCopyQutritWerner
