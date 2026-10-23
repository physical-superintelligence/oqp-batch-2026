module

public import ThreeCopyQutritWerner.CertificateX2InputGen
public import ThreeCopyQutritWerner.CertificateX2InputMeta

@[expose] public section


/-! The symmetry-reduced input tables of the corrected sources of sector 2,
computed at build time from the data in Lean (`x2_input_tables`, CertificateX2InputGen). Build-time data;
identified with the bridge embedding only through the hypothesis hT0 of the transfer theorems. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThreeCopyQutritWerner.X2

x2_input_tables inS2 inA2 2 31603654656000

end ThreeCopyQutritWerner.X2
