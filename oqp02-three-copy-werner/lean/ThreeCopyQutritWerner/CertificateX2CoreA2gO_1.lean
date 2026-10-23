module

public import ThreeCopyQutritWerner.CertificateX2CoreA2gH
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen

@[expose] public section


/-! Batched core A2g: axis-1 stage, row 1. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA2g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_core_stageA_rows o 384 21714 31 transA2Tab h 1 2

end ThreeCopyQutritWerner.X2.CoreA2g
