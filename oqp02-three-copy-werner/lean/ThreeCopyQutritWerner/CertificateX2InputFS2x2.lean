module

public import ThreeCopyQutritWerner.CertificateX2InputDS2
public import ThreeCopyQutritWerner.CertificateX2CoreS2gF0

@[expose] public section


/-! Segment checks of the S2g input table, columns [24, 36). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col24 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 24 1 = true := by decide +kernel
theorem col25 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 25 1 = true := by decide +kernel
theorem col26 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 26 1 = true := by decide +kernel
theorem col27 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 27 1 = true := by decide +kernel
theorem col28 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 28 1 = true := by decide +kernel
theorem col29 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 29 1 = true := by decide +kernel
theorem col30 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 30 1 = true := by decide +kernel
theorem col31 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 31 1 = true := by decide +kernel
theorem col32 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 32 1 = true := by decide +kernel
theorem col33 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 33 1 = true := by decide +kernel
theorem col34 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 34 1 = true := by decide +kernel
theorem col35 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 35 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS2
