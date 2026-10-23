module

public import CGLMPBounds.Defs.ScalarSeries

@[expose] public section


/-!
# The literal integral coefficients and their proposed series representation

Canonical supplement (C.1), (D.6), (I.2). The integral error and the series
error are deliberately distinct definitions.
-/

namespace CGLMPBounds
noncomputable section

def scalarBinomialWeight (d h : ℕ) (x : ℝ) : ℝ :=
  (d.choose h : ℝ) * x ^ h * (1 - x) ^ (d - h)

def scalarBetaTransform (d h : ℕ) (g : ℝ → ℝ) : ℝ :=
  (d : ℝ) * ∫ x in (0 : ℝ)..1, scalarBinomialWeight d h x * g x

def scalarSecant (x : ℝ) : ℝ := 1 / Real.cos (Real.pi * x / 2)

def scalarCorrectionB (x : ℝ) : ℝ :=
  -(1 : ℝ) / 2 * iteratedDeriv 2
    (fun t : ℝ => t * (1 - t) * scalarSecant t - 2 * t / Real.pi) x

/-- The source's e_(d,h), defined by the actual beta integral (D.6). -/
def scalarIntegralError (d h : ℕ) : ℝ :=
  scalarSecant ((h : ℝ) / d) - scalarBetaTransform d h scalarSecant -
    scalarBetaTransform d h scalarCorrectionB / d

/-- The rising-factorial moment m_k printed in Appendix I. -/
def scalarBetaMoment (d h k : ℕ) : ℝ :=
  (d : ℝ) / ((d : ℝ) + 1) * ∏ j ∈ Finset.range k,
    (((d : ℝ) - h + j + 1) / ((d : ℝ) + j + 2))

/-- A single bracket in (I.2), before multiplication by r_n. -/
def scalarErrorBracket (d h k : ℕ) : ℝ :=
  (1 - (h : ℝ) / d) ^ k -
    (1 + ((k : ℝ) + 1) * ((k : ℝ) + 2) / (2 * d)) * scalarBetaMoment d h k +
    (k : ℝ) * ((k : ℝ) + 1) / (2 * d) * scalarBetaMoment d h (k - 1)

/-- The right side of (I.2). Equality with `scalarIntegralError` is a theorem
obligation, not a definitional equality. -/
def scalarSeriesError (d h : ℕ) : ℝ :=
  ∑' i : ℕ, scalarCosecantCoefficient (i + 1) * scalarErrorBracket d h (2 * i + 1)

end
end CGLMPBounds
