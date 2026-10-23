module

public import CGLMPBounds.Defs.ScalarBeta

@[expose] public section


/-! Literal cotangent coefficient in (D.6), with the printed removable value. -/

namespace CGLMPBounds
noncomputable section

def scalarCotangentRemainder (z : ℝ) : ℝ :=
  if z = 0 then 1 / 3 else (1 - z * Real.cot z) / Real.sin z ^ 2

def scalarPartitionS (x : ℝ) : ℝ :=
  scalarCotangentRemainder (Real.pi / 2 * (x - 1 / 2))

def scalarPartitionCoefficient (d h : ℕ) : ℝ :=
  scalarBetaTransform d h scalarPartitionS / d

end
end CGLMPBounds
