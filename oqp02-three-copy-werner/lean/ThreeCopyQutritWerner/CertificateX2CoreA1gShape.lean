module

public import ThreeCopyQutritWerner.CertificateX2CoreA1gT3
public import ThreeCopyQutritWerner.CertificateX2CoreBatchFlat
public import ThreeCopyQutritWerner.CertificateX2Trans
public import ThreeCopyQutritWerner.CertificateX2CoreBatchGen

@[expose] public section


/-! Batched core A1g: shapes of all tables and scalar bounds. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.CoreA1g
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem shapes : transA1Tab.length = 231 ∧ transA1Tab.all (fun r => r.length == 231) = true ∧
    transA1Tab.length = 231 ∧ transA1Tab.all (fun r => r.length == 231) = true ∧
    r0exp.length = 513 ∧ r0exp.all (fun r => r.length == 282) = true ∧
    f0.length = 3 ∧ f0.all (fun r => r.length == 231) = true ∧
    g.length = 3 ∧ g.all (fun r => r.length == 231) = true ∧
    h.length = 3 ∧ h.all (fun r => r.length == 231) = true ∧
    o.length = 3 ∧ o.all (fun r => r.length == 231) = true ∧
    t3.length = 231 ∧ t3.all (fun r => r.length == 231) = true := by
  decide +kernel

theorem scal : transA1Tab.all (fun r => r.all (fun x => Nat.blt x (2 ^ (31 + 1)))) = true ∧
    transA1Tab.all (fun r => r.all (fun x => Nat.blt x (2 ^ (31 + 1)))) = true ∧
    r0exp.all (fun r => r.all (fun x => Nat.blt x (2 ^ (31 + 1)))) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2.CoreA1g
