module

public import ThreeCopyQutritWerner.CertificateX2CoreA2gG
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen

@[expose] public section


/-! Batched core A2g: regrouped table, row 1. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA2g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_core_regroup h 384 282 77 g 231 1 2

end ThreeCopyQutritWerner.X2.CoreA2g
