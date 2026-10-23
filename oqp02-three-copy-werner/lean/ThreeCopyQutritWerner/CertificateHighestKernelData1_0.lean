module

public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel1_0Weight : Fin 3 → ℤ := ![3, 0, -3]

def certificateHighestKernel1_0Rows : Fin 1 → CertificateLocalWord :=
  ![![0, 0, 0, 2, 2, 2]]

def certificateHighestKernel1_0Pivots : Fin 1 → Fin 1 := ![0]

def certificateHighestKernel1_0Tests : Fin 0 → Fin 2 × CertificateLocalWord :=
  Fin.elim0

def certificateHighestKernel1_0U : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel1_0P : Matrix (Fin 1) (Fin 1) ℤ :=
  fun i j => if certificateHighestKernel1_0Pivots i = j then 1 else 0

def certificateHighestKernel1_0R : Matrix (Fin 0) (Fin 1) ℤ :=
  fun i => Fin.elim0 i

def certificateHighestKernel1_0W : Matrix (Fin 1) (Fin 0) ℤ :=
  fun _ j => Fin.elim0 j

def certificateHighestKernel1_0denominator : ℤ := 1

end ThreeCopyQutritWerner
