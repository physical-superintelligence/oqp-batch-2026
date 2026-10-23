module

public import CGLMPBounds.Partition.CountPolynomial
public import CGLMPBounds.Partition.BinomialCoefficients

@[expose] public section


/-! The actual single-mode Fourier-tilted count atom law, with the exact
source second-derivative correction and all natural h. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

theorem fourierBoundaryMeasure_count_law (d n h : ℕ)
    (hd : 2 ≤ d) (hn : 0 < n) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (fourierBoundaryMeasure d n).real {T | boundaryArcCount d origin x T = h} =
      scalarBinomialWeight d h x + fourierTiltShape n x / d *
        iteratedDeriv 2 (scalarBinomialWeight d h) x := by
  apply Complex.ofReal_injective
  rw [fourierBoundaryMeasure_count_eq_coeff d n h hd hn origin x hx,
    fourierCountPolynomial_coeff d n h hd x]

end
end CGLMPBounds.Partition
