module

public import ThreeCopyQutritWerner.CertificateX2CoreS1gG
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen

@[expose] public section


/-! Batched core S1g: regrouped table, row 0. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_core_regroup h 384 282 94 g 282 0 1

end ThreeCopyQutritWerner.X2.CoreS1g
