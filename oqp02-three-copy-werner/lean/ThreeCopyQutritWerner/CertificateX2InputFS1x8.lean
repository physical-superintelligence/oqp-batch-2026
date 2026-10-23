module

public import ThreeCopyQutritWerner.CertificateX2InputDS1
public import ThreeCopyQutritWerner.CertificateX2CoreS1gF0

@[expose] public section


/-! Segment checks of the S1g input table, columns [96, 108). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col96 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 96 1 = true := by decide +kernel
theorem col97 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 97 1 = true := by decide +kernel
theorem col98 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 98 1 = true := by decide +kernel
theorem col99 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 99 1 = true := by decide +kernel
theorem col100 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 100 1 = true := by decide +kernel
theorem col101 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 101 1 = true := by decide +kernel
theorem col102 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 102 1 = true := by decide +kernel
theorem col103 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 103 1 = true := by decide +kernel
theorem col104 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 104 1 = true := by decide +kernel
theorem col105 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 105 1 = true := by decide +kernel
theorem col106 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 106 1 = true := by decide +kernel
theorem col107 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 107 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS1
