module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateLocalHighestChecks
public import ThreeCopyQutritWerner.CertificateLocalFrameMetrics

@[expose] public section


/-! Exact highest-kernel candidate data. No property is assumed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

def certificateHighestKernel2_5Weight : Fin 3 → ℤ := ![0, -2, -2]

def certificateHighestKernel2_5Rows : Fin 50 → CertificateLocalWord :=
  ![![0, 0, 1, 1, 2, 2],
    ![0, 0, 1, 2, 1, 2],
    ![0, 0, 1, 2, 2, 1],
    ![0, 0, 2, 1, 1, 2],
    ![0, 0, 2, 1, 2, 1],
    ![0, 0, 2, 2, 1, 1],
    ![0, 1, 0, 1, 2, 2],
    ![0, 1, 0, 2, 1, 2],
    ![0, 1, 0, 2, 2, 1],
    ![0, 1, 1, 0, 2, 2],
    ![0, 1, 1, 2, 0, 2],
    ![0, 1, 1, 2, 2, 0],
    ![0, 1, 2, 0, 1, 2],
    ![0, 1, 2, 0, 2, 1],
    ![0, 1, 2, 1, 0, 2],
    ![0, 1, 2, 1, 2, 0],
    ![0, 1, 2, 2, 0, 1],
    ![0, 1, 2, 2, 1, 0],
    ![0, 2, 0, 1, 1, 2],
    ![0, 2, 0, 1, 2, 1],
    ![0, 2, 0, 2, 1, 1],
    ![0, 2, 1, 0, 1, 2],
    ![0, 2, 1, 0, 2, 1],
    ![0, 2, 1, 1, 0, 2],
    ![0, 2, 1, 1, 2, 0],
    ![0, 2, 1, 2, 0, 1],
    ![0, 2, 1, 2, 1, 0],
    ![0, 2, 2, 0, 1, 1],
    ![0, 2, 2, 1, 0, 1],
    ![0, 2, 2, 1, 1, 0],
    ![1, 1, 1, 1, 2, 2],
    ![1, 1, 1, 2, 1, 2],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 1, 1, 2],
    ![1, 1, 2, 1, 2, 1],
    ![1, 1, 2, 2, 1, 1],
    ![1, 2, 1, 1, 1, 2],
    ![1, 2, 1, 1, 2, 1],
    ![1, 2, 1, 2, 1, 1],
    ![1, 2, 2, 1, 1, 1],
    ![2, 1, 1, 2, 2, 2],
    ![2, 1, 2, 1, 2, 2],
    ![2, 1, 2, 2, 1, 2],
    ![2, 1, 2, 2, 2, 1],
    ![2, 2, 1, 1, 2, 2],
    ![2, 2, 1, 2, 1, 2],
    ![2, 2, 1, 2, 2, 1],
    ![2, 2, 2, 1, 1, 2],
    ![2, 2, 2, 1, 2, 1],
    ![2, 2, 2, 2, 1, 1]]

def certificateHighestKernel2_5Pivots : Fin 10 → Fin 50 := ![12,
    14,
    15,
    10,
    11,
    34,
    33,
    32,
    31,
    30]

def certificateHighestKernel2_5Tests : Fin 40 → Fin 2 × CertificateLocalWord :=
  ![(0, ![0, 1, 1, 1, 2, 2]),
    (0, ![0, 1, 1, 2, 1, 2]),
    (0, ![0, 1, 1, 2, 2, 1]),
    (0, ![0, 1, 2, 1, 1, 2]),
    (0, ![0, 1, 2, 1, 2, 1]),
    (0, ![0, 1, 2, 2, 1, 1]),
    (0, ![0, 2, 1, 1, 1, 2]),
    (0, ![0, 2, 1, 1, 2, 1]),
    (0, ![0, 2, 1, 2, 1, 1]),
    (0, ![0, 2, 2, 1, 1, 1]),
    (1, ![0, 0, 1, 2, 2, 2]),
    (1, ![0, 0, 2, 1, 2, 2]),
    (1, ![0, 0, 2, 2, 1, 2]),
    (1, ![0, 0, 2, 2, 2, 1]),
    (1, ![0, 1, 0, 2, 2, 2]),
    (1, ![0, 1, 2, 0, 2, 2]),
    (1, ![0, 1, 2, 2, 0, 2]),
    (1, ![0, 1, 2, 2, 2, 0]),
    (1, ![0, 2, 0, 1, 2, 2]),
    (1, ![0, 2, 0, 2, 1, 2]),
    (1, ![0, 2, 0, 2, 2, 1]),
    (1, ![0, 2, 1, 0, 2, 2]),
    (1, ![0, 2, 1, 2, 0, 2]),
    (1, ![0, 2, 1, 2, 2, 0]),
    (1, ![0, 2, 2, 0, 1, 2]),
    (1, ![0, 2, 2, 0, 2, 1]),
    (1, ![0, 2, 2, 1, 0, 2]),
    (1, ![0, 2, 2, 1, 2, 0]),
    (1, ![0, 2, 2, 2, 0, 1]),
    (1, ![0, 2, 2, 2, 1, 0]),
    (1, ![1, 1, 1, 2, 2, 2]),
    (1, ![1, 1, 2, 1, 2, 2]),
    (1, ![1, 1, 2, 2, 1, 2]),
    (1, ![1, 1, 2, 2, 2, 1]),
    (1, ![1, 2, 1, 1, 2, 2]),
    (1, ![1, 2, 1, 2, 1, 2]),
    (1, ![1, 2, 1, 2, 2, 1]),
    (1, ![1, 2, 2, 1, 1, 2]),
    (1, ![1, 2, 2, 1, 2, 1]),
    (1, ![1, 2, 2, 2, 1, 1])]

def certificateHighestKernel2_5U : Matrix (Fin 50) (Fin 10) ℤ :=
  certificate_matrix% "verification/matrix-literals/ee51e527e2fd607684b98c07bca56287672a63ea191652788bf3de1c2f971c10.xz" "f5cdd22e7755bc38c815736f9edde834275eb2030b315fc3d58a3100b2db0d17"

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel2_5P : Matrix (Fin 10) (Fin 50) ℤ :=
  fun i j => if certificateHighestKernel2_5Pivots i = j then 1 else 0

def certificateHighestKernel2_5R : Matrix (Fin 40) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/7cd77e31dab1322e35ab6aa1d9b690500606d25c93744def18340e7ef8caa776.xz" "c8cb9fca13f352ce0f4ec104b729ccda5076883883ec77d607e256c300f7db1f"

def certificateHighestKernel2_5W : Matrix (Fin 50) (Fin 40) ℤ :=
  certificate_matrix% "verification/matrix-literals/6b1e8183945eb8a7f973aacd299ac1daea5b63782114c67d2496fb1ac21529d3.xz" "a5951472fcfe58bb26d5310ff4ccf4fa1ee2d23ff633d7aa34a37cce537ffb45"

def certificateHighestKernel2_5denominator : ℤ := 2

end ThreeCopyQutritWerner
