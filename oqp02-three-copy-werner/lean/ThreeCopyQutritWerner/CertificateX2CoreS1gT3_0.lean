module

public import ThreeCopyQutritWerner.CertificateX2CoreS1gO
public import ThreeCopyQutritWerner.CertificateX2CoreS1gCs

@[expose] public section


/-! Batched core S1g: axis-0 stage, rows 0..22. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreS1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

x2_core_stageC_sub t3 384 282 513 94 cs o 282 tl tl 0 23

end ThreeCopyQutritWerner.X2.CoreS1g
