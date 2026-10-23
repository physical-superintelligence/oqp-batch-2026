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

def certificateHighestKernel1_6Weight : Fin 3 → ℤ := ![1, 0, -1]

def certificateHighestKernel1_6Rows : Fin 60 → CertificateLocalWord :=
  ![![0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 2, 0, 0],
    ![0, 0, 1, 0, 1, 2],
    ![0, 0, 1, 0, 2, 1],
    ![0, 0, 1, 1, 0, 2],
    ![0, 0, 1, 1, 2, 0],
    ![0, 0, 1, 2, 0, 1],
    ![0, 0, 1, 2, 1, 0],
    ![0, 0, 2, 0, 2, 2],
    ![0, 0, 2, 2, 0, 2],
    ![0, 0, 2, 2, 2, 0],
    ![0, 1, 0, 0, 1, 2],
    ![0, 1, 0, 0, 2, 1],
    ![0, 1, 0, 1, 0, 2],
    ![0, 1, 0, 1, 2, 0],
    ![0, 1, 0, 2, 0, 1],
    ![0, 1, 0, 2, 1, 0],
    ![0, 1, 1, 1, 1, 2],
    ![0, 1, 1, 1, 2, 1],
    ![0, 1, 1, 2, 1, 1],
    ![0, 1, 2, 1, 2, 2],
    ![0, 1, 2, 2, 1, 2],
    ![0, 1, 2, 2, 2, 1],
    ![0, 2, 0, 0, 2, 2],
    ![0, 2, 0, 2, 0, 2],
    ![0, 2, 0, 2, 2, 0],
    ![0, 2, 1, 1, 2, 2],
    ![0, 2, 1, 2, 1, 2],
    ![0, 2, 1, 2, 2, 1],
    ![0, 2, 2, 2, 2, 2],
    ![1, 0, 0, 0, 1, 2],
    ![1, 0, 0, 0, 2, 1],
    ![1, 0, 0, 1, 0, 2],
    ![1, 0, 0, 1, 2, 0],
    ![1, 0, 0, 2, 0, 1],
    ![1, 0, 0, 2, 1, 0],
    ![1, 0, 1, 1, 1, 2],
    ![1, 0, 1, 1, 2, 1],
    ![1, 0, 1, 2, 1, 1],
    ![1, 0, 2, 1, 2, 2],
    ![1, 0, 2, 2, 1, 2],
    ![1, 0, 2, 2, 2, 1],
    ![1, 1, 0, 1, 1, 2],
    ![1, 1, 0, 1, 2, 1],
    ![1, 1, 0, 2, 1, 1],
    ![1, 2, 0, 1, 2, 2],
    ![1, 2, 0, 2, 1, 2],
    ![1, 2, 0, 2, 2, 1],
    ![2, 0, 0, 0, 2, 2],
    ![2, 0, 0, 2, 0, 2],
    ![2, 0, 0, 2, 2, 0],
    ![2, 0, 1, 1, 2, 2],
    ![2, 0, 1, 2, 1, 2],
    ![2, 0, 1, 2, 2, 1],
    ![2, 0, 2, 2, 2, 2],
    ![2, 1, 0, 1, 2, 2],
    ![2, 1, 0, 2, 1, 2],
    ![2, 1, 0, 2, 2, 1],
    ![2, 2, 0, 2, 2, 2]]

def certificateHighestKernel1_6Pivots : Fin 17 → Fin 60 := ![17,
    22,
    23,
    28,
    29,
    30,
    36,
    41,
    42,
    47,
    48,
    53,
    54,
    55,
    57,
    58,
    59]

def certificateHighestKernel1_6Tests : Fin 43 → Fin 2 × CertificateLocalWord :=
  ![(0, ![0, 0, 0, 0, 1, 2]),
    (0, ![0, 0, 0, 0, 2, 1]),
    (0, ![0, 0, 0, 1, 0, 2]),
    (0, ![0, 0, 0, 1, 2, 0]),
    (0, ![0, 0, 0, 2, 0, 1]),
    (0, ![0, 0, 0, 2, 1, 0]),
    (0, ![0, 0, 1, 1, 1, 2]),
    (0, ![0, 0, 1, 1, 2, 1]),
    (0, ![0, 0, 1, 2, 1, 1]),
    (0, ![0, 0, 2, 1, 2, 2]),
    (0, ![0, 0, 2, 2, 1, 2]),
    (0, ![0, 0, 2, 2, 2, 1]),
    (0, ![0, 1, 0, 1, 1, 2]),
    (0, ![0, 1, 0, 1, 2, 1]),
    (0, ![0, 1, 0, 2, 1, 1]),
    (0, ![0, 2, 0, 1, 2, 2]),
    (0, ![0, 2, 0, 2, 1, 2]),
    (0, ![0, 2, 0, 2, 2, 1]),
    (0, ![1, 0, 0, 1, 1, 2]),
    (0, ![1, 0, 0, 1, 2, 1]),
    (0, ![1, 0, 0, 2, 1, 1]),
    (0, ![2, 0, 0, 1, 2, 2]),
    (0, ![2, 0, 0, 2, 1, 2]),
    (0, ![2, 0, 0, 2, 2, 1]),
    (1, ![0, 0, 1, 0, 2, 2]),
    (1, ![0, 0, 1, 2, 0, 2]),
    (1, ![0, 0, 1, 2, 2, 0]),
    (1, ![0, 1, 0, 0, 2, 2]),
    (1, ![0, 1, 0, 2, 0, 2]),
    (1, ![0, 1, 0, 2, 2, 0]),
    (1, ![0, 1, 1, 1, 2, 2]),
    (1, ![0, 1, 1, 2, 1, 2]),
    (1, ![0, 1, 1, 2, 2, 1]),
    (1, ![0, 1, 2, 2, 2, 2]),
    (1, ![0, 2, 1, 2, 2, 2]),
    (1, ![1, 0, 0, 0, 2, 2]),
    (1, ![1, 0, 0, 2, 0, 2]),
    (1, ![1, 0, 0, 2, 2, 0]),
    (1, ![1, 0, 1, 1, 2, 2]),
    (1, ![1, 0, 1, 2, 1, 2]),
    (1, ![1, 0, 1, 2, 2, 1]),
    (1, ![1, 0, 2, 2, 2, 2]),
    (1, ![1, 2, 0, 2, 2, 2])]

def certificateHighestKernel1_6U : Matrix (Fin 60) (Fin 17) ℤ :=
  certificate_matrix% "verification/matrix-literals/1fa871b3ce7a880d738ccc7e61ad239adbf1a1c11b3baaf7b85e1339e4a07ddd.xz" "e4a420778f8e42622c30792ea4808cbda52ad5f14072a7d1e3c21c4c0656bf38"

/-- Projection onto the original identity-row source coordinates. -/
def certificateHighestKernel1_6P : Matrix (Fin 17) (Fin 60) ℤ :=
  fun i j => if certificateHighestKernel1_6Pivots i = j then 1 else 0

def certificateHighestKernel1_6R : Matrix (Fin 43) (Fin 60) ℤ :=
  certificate_matrix% "verification/matrix-literals/f3a7988b30ba570a4cb89c9bfc7c08776eb419065c6c3ed560f90af64455ae0f.xz" "4682666b05c43da83a06f312e355d619e2bbea6f2f227f3b7c15bdb7c0c1ca87"

def certificateHighestKernel1_6W : Matrix (Fin 60) (Fin 43) ℤ :=
  certificate_matrix% "verification/matrix-literals/14781614d765347467093ed9f4467a7d427618c45e07e8e2322eecf041775b8d.xz" "176d0c37280b30aa68ce7c48ddc9ffba170f4b07ea6ac29da645bfac08e8afe2"

def certificateHighestKernel1_6denominator : ℤ := 2

end ThreeCopyQutritWerner
