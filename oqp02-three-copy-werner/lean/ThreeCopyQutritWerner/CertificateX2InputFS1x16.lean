module

public import ThreeCopyQutritWerner.CertificateX2InputDS1
public import ThreeCopyQutritWerner.CertificateX2CoreS1gF0

@[expose] public section


/-! Segment checks of the S1g input table, columns [192, 204). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace ThreeCopyQutritWerner.X2.InFS1
open ThreeCopyQutritWerner ThreeCopyQutritWerner.X2

theorem col192 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 192 1 = true := by decide +kernel
theorem col193 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 193 1 = true := by decide +kernel
theorem col194 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 194 1 = true := by decide +kernel
theorem col195 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 195 1 = true := by decide +kernel
theorem col196 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 196 1 = true := by decide +kernel
theorem col197 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 197 1 = true := by decide +kernel
theorem col198 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 198 1 = true := by decide +kernel
theorem col199 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 199 1 = true := by decide +kernel
theorem col200 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 200 1 = true := by decide +kernel
theorem col201 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 201 1 = true := by decide +kernel
theorem col202 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 202 1 = true := by decide +kernel
theorem col203 : colsChunkOK 1 InDS1.TTd InDS1.TCd InDS1.Zd CoreS1g.f0 203 1 = true := by decide +kernel

end ThreeCopyQutritWerner.X2.InFS1
