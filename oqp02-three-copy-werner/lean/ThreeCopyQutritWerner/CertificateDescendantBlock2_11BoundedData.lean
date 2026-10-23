module

public import ThreeCopyQutritWerner.CertificateMatrixLiteral
public import ThreeCopyQutritWerner.CertificateDescendantData

@[expose] public section


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open scoped Matrix

namespace ThreeCopyQutritWerner

def certificateDescendantBlockA2_11 : Matrix (Fin 80) (Fin 80) ℤ :=
  certificate_matrix% "verification/matrix-literals/34efc83fef6cb7defc36d35887d82651005ccc394026190aec9502958312d4d4.xz" "dd472bc9db3406889816ab7d5ff608d7ff622eb34c4e00babd3a058fdc841a3e"

def certificateDescendantBlockW2_11 : Matrix (Fin 80) (Fin 80) ℤ :=
  certificate_matrix% "verification/matrix-literals/c69b1cf2ade80b604839162849be296f5ea5d3386380fe8ec698596d5613194d.xz" "e8593c3d3bd08cb87e33a06d8dd3e79b0095b33f8726d6b8f6afce26022567b0"

end ThreeCopyQutritWerner
