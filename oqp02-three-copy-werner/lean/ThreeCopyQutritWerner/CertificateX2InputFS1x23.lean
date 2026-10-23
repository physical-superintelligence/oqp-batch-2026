module

public import ThreeCopyQutritWerner.CertificateX2InputDS1
public import ThreeCopyQutritWerner.CertificateX2CoreS1gF0

@[expose] public section


/-! Segment checks of the S1g input table, columns [276, 282). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col276 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 276 1 = true := by decide +kernel
theorem col277 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 277 1 = true := by decide +kernel
theorem col278 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 278 1 = true := by decide +kernel
theorem col279 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 279 1 = true := by decide +kernel
theorem col280 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 280 1 = true := by decide +kernel
theorem col281 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 281 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS1
