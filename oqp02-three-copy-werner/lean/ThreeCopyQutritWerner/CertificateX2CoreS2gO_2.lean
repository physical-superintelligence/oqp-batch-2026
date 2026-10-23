module

public import ThreeCopyQutritWerner.CertificateX2CoreS2gH
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen

@[expose] public section


/-! Batched core S2g: axis-1 stage, row 2. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS2g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_core_stageA_rows o 384 26508 31 transS2Tab h 2 3

end ThreeCopyQutritWerner.X2.CoreS2g
