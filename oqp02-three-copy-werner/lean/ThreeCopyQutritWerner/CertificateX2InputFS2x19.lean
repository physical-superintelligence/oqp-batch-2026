module

public import ThreeCopyQutritWerner.CertificateX2InputDS2
public import ThreeCopyQutritWerner.CertificateX2CoreS2gF0

@[expose] public section


/-! Segment checks of the S2g input table, columns [228, 240). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col228 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 228 1 = true := by decide +kernel
theorem col229 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 229 1 = true := by decide +kernel
theorem col230 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 230 1 = true := by decide +kernel
theorem col231 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 231 1 = true := by decide +kernel
theorem col232 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 232 1 = true := by decide +kernel
theorem col233 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 233 1 = true := by decide +kernel
theorem col234 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 234 1 = true := by decide +kernel
theorem col235 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 235 1 = true := by decide +kernel
theorem col236 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 236 1 = true := by decide +kernel
theorem col237 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 237 1 = true := by decide +kernel
theorem col238 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 238 1 = true := by decide +kernel
theorem col239 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 239 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS2
