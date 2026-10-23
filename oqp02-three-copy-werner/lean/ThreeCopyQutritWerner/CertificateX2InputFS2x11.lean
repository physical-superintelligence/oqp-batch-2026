module

public import ThreeCopyQutritWerner.CertificateX2InputDS2
public import ThreeCopyQutritWerner.CertificateX2CoreS2gF0

@[expose] public section


/-! Segment checks of the S2g input table, columns [132, 144). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col132 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 132 1 = true := by decide +kernel
theorem col133 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 133 1 = true := by decide +kernel
theorem col134 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 134 1 = true := by decide +kernel
theorem col135 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 135 1 = true := by decide +kernel
theorem col136 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 136 1 = true := by decide +kernel
theorem col137 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 137 1 = true := by decide +kernel
theorem col138 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 138 1 = true := by decide +kernel
theorem col139 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 139 1 = true := by decide +kernel
theorem col140 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 140 1 = true := by decide +kernel
theorem col141 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 141 1 = true := by decide +kernel
theorem col142 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 142 1 = true := by decide +kernel
theorem col143 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 143 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS2
