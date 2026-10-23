module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_16 : Matrix (Fin 80) (Fin 80) ℤ :=
  certificate_matrix% "verification/matrix-literals/e5ce00f0e89bf5b881e41ea3fba973d7e5c18ecb04454f98c114cdce428a5224.xz" "2d754df120da7ada9286766c1e7f459423fbb45699db482908bf1e85cfa8a949"

def certificateDescendantBlockW2_16 : Matrix (Fin 80) (Fin 80) ℤ :=
  certificate_matrix% "verification/matrix-literals/8e8ddecb42447e5740806ece64b5266c5331c5837df24878a7db9e8a27650d55.xz" "b9d5b0ae1ae2687add9ef3607ece6fa02e16900e6d41b95ceaaec5ad34c7692d"

end ThreeCopyQutritWerner
