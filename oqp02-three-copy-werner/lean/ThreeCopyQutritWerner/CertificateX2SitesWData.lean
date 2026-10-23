module

public import ThreeCopyQutritWerner.CertificateX2PackedLiteral

@[expose] public section


/-! Unit-weight numerator tables (row `u`, entry `p`: `Wnum_s[p, u] + 2^25`). Data only. -/

namespace ThreeCopyQutritWerner.X2Sites

x2_nat_table x2sW1 "verification/matrix-literals/x2-sites/w1.hex"
x2_nat_table x2sW2 "verification/matrix-literals/x2-sites/w2.hex"

end ThreeCopyQutritWerner.X2Sites
