module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_17 : Matrix (Fin 80) (Fin 80) ℤ :=
  certificate_matrix% "verification/matrix-literals/bc255a50ffd884690ace22b9aaf534a822e9f4b6546b177925e48cfae4040cfc.xz" "48f374882aede25e24dd31d3ae2abd8f606565feb272e2e31fbf03d9bccf11a1"

def certificateDescendantBlockW2_17 : Matrix (Fin 80) (Fin 80) ℤ :=
  certificate_matrix% "verification/matrix-literals/b06193649e4108f6d13e4dac5e080038fcb9a2b4d019dcb6c5d1103edade3980.xz" "98327ce0591c077147de8fb1b8b3b467ab14fb5b77e066458437f1107afe8a25"

end ThreeCopyQutritWerner
