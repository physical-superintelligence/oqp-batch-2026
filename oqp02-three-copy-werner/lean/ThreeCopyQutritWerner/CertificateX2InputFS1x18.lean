module

public import ThreeCopyQutritWerner.CertificateX2InputDS1
public import ThreeCopyQutritWerner.CertificateX2CoreS1gF0

@[expose] public section


/-! Segment checks of the S1g input table, columns [216, 228). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col216 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 216 1 = true := by decide +kernel
theorem col217 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 217 1 = true := by decide +kernel
theorem col218 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 218 1 = true := by decide +kernel
theorem col219 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 219 1 = true := by decide +kernel
theorem col220 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 220 1 = true := by decide +kernel
theorem col221 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 221 1 = true := by decide +kernel
theorem col222 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 222 1 = true := by decide +kernel
theorem col223 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 223 1 = true := by decide +kernel
theorem col224 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 224 1 = true := by decide +kernel
theorem col225 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 225 1 = true := by decide +kernel
theorem col226 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 226 1 = true := by decide +kernel
theorem col227 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 227 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS1
