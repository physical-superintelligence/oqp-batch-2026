module

public import ThreeCopyQutritWerner.CertificateX2InputDS2
public import ThreeCopyQutritWerner.CertificateX2CoreS2gF0

@[expose] public section


/-! Segment checks of the S2g input table, columns [252, 264). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS2
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col252 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 252 1 = true := by decide +kernel
theorem col253 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 253 1 = true := by decide +kernel
theorem col254 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 254 1 = true := by decide +kernel
theorem col255 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 255 1 = true := by decide +kernel
theorem col256 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 256 1 = true := by decide +kernel
theorem col257 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 257 1 = true := by decide +kernel
theorem col258 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 258 1 = true := by decide +kernel
theorem col259 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 259 1 = true := by decide +kernel
theorem col260 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 260 1 = true := by decide +kernel
theorem col261 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 261 1 = true := by decide +kernel
theorem col262 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 262 1 = true := by decide +kernel
theorem col263 : colsChunkOK 2 InDS2.TTd InDS2.TCd InDS2.Zd CoreS2g.f0 263 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS2
