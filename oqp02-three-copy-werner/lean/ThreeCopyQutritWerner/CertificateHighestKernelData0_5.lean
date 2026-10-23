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

def certificateHighestKernel0_5Weight : Fin 3 → ℤ := ![0, -2, -2]

def certificateHighestKernel0_5Rows : Fin 50 → CertificateLocalWord :=
  ![![0, 1, 1, 2, 2, 0],
    ![0, 1, 2, 1, 2, 0],
    ![0, 1, 2, 2, 1, 0],
    ![0, 2, 1, 1, 2, 0],
    ![0, 2, 1, 2, 1, 0],
    ![0, 2, 2, 1, 1, 0],
    ![1, 0, 1, 2, 2, 0],
    ![1, 0, 2, 1, 2, 0],
    ![1, 0, 2, 2, 1, 0],
    ![1, 1, 0, 2, 2, 0],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 0, 2, 0],
    ![1, 1, 2, 1, 2, 1],
    ![1, 1, 2, 2, 0, 0],
    ![1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 2],
    ![1, 2, 0, 1, 2, 0],
    ![1, 2, 0, 2, 1, 0],
    ![1, 2, 1, 0, 2, 0],
    ![1, 2, 1, 1, 2, 1],
    ![1, 2, 1, 2, 0, 0],
    ![1, 2, 1, 2, 1, 1],
    ![1, 2, 1, 2, 2, 2],
    ![1, 2, 2, 0, 1, 0],
    ![1, 2, 2, 1, 0, 0],
    ![1, 2, 2, 1, 1, 1],
    ![1, 2, 2, 1, 2, 2],
    ![1, 2, 2, 2, 1, 2],
    ![2, 0, 1, 1, 2, 0],
    ![2, 0, 1, 2, 1, 0],
    ![2, 0, 2, 1, 1, 0],
    ![2, 1, 0, 1, 2, 0],
    ![2, 1, 0, 2, 1, 0],
    ![2, 1, 1, 0, 2, 0],
    ![2, 1, 1, 1, 2, 1],
    ![2, 1, 1, 2, 0, 0],
    ![2, 1, 1, 2, 1, 1],
    ![2, 1, 1, 2, 2, 2],
    ![2, 1, 2, 0, 1, 0],
    ![2, 1, 2, 1, 0, 0],
    ![2, 1, 2, 1, 1, 1],
    ![2, 1, 2, 1, 2, 2],
    ![2, 1, 2, 2, 1, 2],
    ![2, 2, 0, 1, 1, 0],
    ![2, 2, 1, 0, 1, 0],
    ![2, 2, 1, 1, 0, 0],
    ![2, 2, 1, 1, 1, 1],
    ![2, 2, 1, 1, 2, 2],
    ![2, 2, 1, 2, 1, 2],
    ![2, 2, 2, 1, 1, 2]]

def certificateHighestKernel0_5Pivots : Fin 10 → Fin 50 := ![18,
    20,
    1,
    24,
    0,
    12,
    22,
    10,
    26,
    27]

def certificateHighestKernel0_5Tests : Fin 40 → Fin 2 × CertificateLocalWord :=
  ![(0, ![1, 1, 1, 2, 2, 0]),
    (0, ![1, 1, 2, 1, 2, 0]),
    (0, ![1, 1, 2, 2, 1, 0]),
    (0, ![1, 2, 1, 1, 2, 0]),
    (0, ![1, 2, 1, 2, 1, 0]),
    (0, ![1, 2, 2, 1, 1, 0]),
    (0, ![2, 1, 1, 1, 2, 0]),
    (0, ![2, 1, 1, 2, 1, 0]),
    (0, ![2, 1, 2, 1, 1, 0]),
    (0, ![2, 2, 1, 1, 1, 0]),
    (1, ![0, 1, 2, 2, 2, 0]),
    (1, ![0, 2, 1, 2, 2, 0]),
    (1, ![0, 2, 2, 1, 2, 0]),
    (1, ![0, 2, 2, 2, 1, 0]),
    (1, ![1, 0, 2, 2, 2, 0]),
    (1, ![1, 1, 2, 2, 2, 1]),
    (1, ![1, 2, 0, 2, 2, 0]),
    (1, ![1, 2, 1, 2, 2, 1]),
    (1, ![1, 2, 2, 0, 2, 0]),
    (1, ![1, 2, 2, 1, 2, 1]),
    (1, ![1, 2, 2, 2, 0, 0]),
    (1, ![1, 2, 2, 2, 1, 1]),
    (1, ![2, 0, 1, 2, 2, 0]),
    (1, ![2, 0, 2, 1, 2, 0]),
    (1, ![2, 0, 2, 2, 1, 0]),
    (1, ![2, 1, 0, 2, 2, 0]),
    (1, ![2, 1, 1, 2, 2, 1]),
    (1, ![2, 1, 2, 0, 2, 0]),
    (1, ![2, 1, 2, 1, 2, 1]),
    (1, ![2, 1, 2, 2, 0, 0]),
    (1, ![2, 1, 2, 2, 1, 1]),
    (1, ![2, 2, 0, 1, 2, 0]),
    (1, ![2, 2, 0, 2, 1, 0]),
    (1, ![2, 2, 1, 0, 2, 0]),
    (1, ![2, 2, 1, 1, 2, 1]),
    (1, ![2, 2, 1, 2, 0, 0]),
    (1, ![2, 2, 1, 2, 1, 1]),
    (1, ![2, 2, 2, 0, 1, 0]),
    (1, ![2, 2, 2, 1, 0, 0]),
    (1, ![2, 2, 2, 1, 1, 1])]

def certificateHighestKernel0_5U : Matrix (Fin 50) (Fin 10) ℤ :=
  certificate_matrix% "verification/matrix-literals/651aaf006beee9319a4c33cf8b222ca036838c8e0e3c26a82c85c82cd7245ebf.xz" "ebbb0095760fdf4c5322af0ba6bf9f7ca73152d42a0fe79d93e86b33f2921549"

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel0_5P : Matrix (Fin 10) (Fin 50) ℤ :=
  fun i j => if certificateHighestKernel0_5Pivots i = j then 1 else 0

def certificateHighestKernel0_5R : Matrix (Fin 40) (Fin 50) ℤ :=
  certificate_matrix% "verification/matrix-literals/8ca89619be11a4e3ed5b891d575322c490c3563f165d6bed0cc458d2c229318b.xz" "09133a32cdd6b178165c7b0b520e847e14cae6dfdacb21f55a4933273713bb43"

def certificateHighestKernel0_5W : Matrix (Fin 50) (Fin 40) ℤ :=
  certificate_matrix% "verification/matrix-literals/cd82540c31ebfe760812fa9faf511cf142f084c3b529ba3fb8b3f2ad0c80bc88.xz" "682054ceea0b48eee6402e65a7bf5fff2a9fbeaaa51d7aa3da5adccb2af0319c"

def certificateHighestKernel0_5denominator : ℤ := 2

end ThreeCopyQutritWerner
