module

public import CGLMPBounds.Defs.PartitionProbability

@[expose] public section


/-! Literal finite count probability polynomials. Coefficients of the first
polynomial are actual atom masses of a measure; no distributional law is
assumed. The other polynomials encode the source single-mode formulas. -/

namespace CGLMPBounds.Partition
open MeasureTheory Polynomial
noncomputable section

def finiteCountPolynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (d : ℕ) : Polynomial ℂ :=
  ∑ h ∈ Finset.range (d + 1), Polynomial.monomial h (μ.real {ω | N ω = h} : ℂ)

def boundaryBinomialPolynomial (d : ℕ) (x : ℝ) : Polynomial ℂ :=
  (Polynomial.C ((1 - x : ℝ) : ℂ) + Polynomial.C (x : ℂ) * Polynomial.X) ^ d

def fourierCountPolynomial (d n : ℕ) (x : ℝ) : Polynomial ℂ :=
  boundaryBinomialPolynomial d x +
    Polynomial.C (((d : ℂ) - 1) * (fourierTiltShape n x : ℂ)) *
      (Polynomial.X - 1) ^ 2 * boundaryBinomialPolynomial (d - 2) x

end
end CGLMPBounds.Partition
