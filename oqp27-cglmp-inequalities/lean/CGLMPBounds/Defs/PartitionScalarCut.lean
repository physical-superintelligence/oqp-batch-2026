module

public import CGLMPBounds.Defs.PartitionHardy

@[expose] public section


/-! The literal scalar branch in supplement D.4. Multiplication writes the
integer power as i^(-a) times the jump i; this is exactly i^(-a+1_{t>T}).
No translation invariance or Fourier-energy equality is built in. -/

namespace CGLMPBounds.Partition
noncomputable section

def sourceScalarCutBranch (a : ℤ) (T t : ℝ) : ℂ :=
  Complex.exp (((-Real.pi * t / 2 : ℝ) : ℂ) * Complex.I) *
    Complex.I ^ (-a) * (if T < t then Complex.I else 1)

end
end CGLMPBounds.Partition
