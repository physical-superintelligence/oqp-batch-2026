module

public import CGLMPBounds.Defs.ScalarBeta

@[expose] public section


/-! The literal skew scalar coefficients and triangle combination in (D.13). -/

namespace CGLMPBounds
noncomputable section

def scalarErrorSkew (d h : ℕ) : ℝ :=
  scalarIntegralError d (d - h) - scalarIntegralError d h

def scalarErrorTriangle (d i j k : ℕ) : ℝ :=
  scalarErrorSkew d (j - i) + scalarErrorSkew d (k - j) - scalarErrorSkew d (k - i)

end
end CGLMPBounds
