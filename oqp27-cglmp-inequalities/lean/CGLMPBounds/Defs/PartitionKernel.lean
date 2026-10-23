module

public import CGLMPBounds.Defs.PartitionHardy

@[expose] public section


/-! The Abel-damped scalar kernel obtained from the actual negative
Fourier modes of the quarter-root branch. It is a literal infinite sum;
its geometric-series value and secant limit are theorem obligations. -/

namespace CGLMPBounds.Partition
noncomputable section

def quarterBranchAbelKernel (q x : ℝ) : ℂ :=
  ∑' n : ℕ, (q : ℂ) ^ n *
    Complex.exp ((((2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * x : ℝ) : ℂ) *
      Complex.I)

end
end CGLMPBounds.Partition
