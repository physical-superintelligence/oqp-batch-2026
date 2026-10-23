module

public import CGLMPBounds.Defs.PartitionCount
public import CGLMPBounds.Partition.TiltedMeasureIntegrals

@[expose] public section


/-! Finite count coefficients are actual atom probabilities. The actual
Fourier-tilted measure's polynomial is identified without assuming any atom
law or derivative formula. -/

namespace CGLMPBounds.Partition
open MeasureTheory Polynomial
noncomputable section

theorem measurable_boundaryArcCount (d : ℕ) (origin x : ℝ) :
    Measurable (boundaryArcCount d origin x) := by
  classical
  unfold boundaryArcCount
  simp only [Finset.card_filter]
  apply Finset.measurable_fun_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    measurable_const measurable_const

theorem integral_pow_finite_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : Ω → ℕ) (d : ℕ)
    (hN : Measurable N) (hbound : ∀ ω, N ω ≤ d) (z : ℂ) :
    (∫ ω, z ^ N ω ∂μ) =
      ∑ h ∈ Finset.range (d + 1), (μ.real {ω | N ω = h} : ℂ) * z ^ h := by
  classical
  have hs (h : ℕ) : MeasurableSet {ω | N ω = h} := hN (measurableSet_singleton h)
  have hpoint (ω : Ω) : z ^ N ω =
      ∑ h ∈ Finset.range (d + 1), {ω | N ω = h}.indicator (fun _ => z ^ h) ω := by
    simp [Set.indicator_apply, Finset.mem_range, Nat.lt_succ_of_le (hbound ω)]
  calc
    _ = ∫ ω, ∑ h ∈ Finset.range (d + 1),
        {ω | N ω = h}.indicator (fun _ => z ^ h) ω ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∑ h ∈ Finset.range (d + 1),
        ∫ ω, {ω | N ω = h}.indicator (fun _ => z ^ h) ω ∂μ :=
      integral_finsetSum _ (fun h _ => (integrable_const (z ^ h)).indicator (hs h))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_indicator_const _ (hs h), Complex.real_smul]

theorem finiteCountPolynomial_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (N : Ω → ℕ) (d : ℕ)
    (hN : Measurable N) (hbound : ∀ ω, N ω ≤ d) (z : ℂ) :
    (finiteCountPolynomial μ N d).eval z = ∫ ω, z ^ N ω ∂μ := by
  rw [integral_pow_finite_count μ N d hN hbound z]
  simp only [finiteCountPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem finiteCountPolynomial_coeff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℕ) (d h : ℕ) (hbound : ∀ ω, N ω ≤ d) :
    (finiteCountPolynomial μ N d).coeff h = (μ.real {ω | N ω = h} : ℂ) := by
  classical
  by_cases hh : h < d + 1
  · simp [finiteCountPolynomial, Polynomial.coeff_monomial, hh]
  · have hempty : {ω | N ω = h} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      have hb := hbound ω
      omega
    simp [finiteCountPolynomial, Polynomial.coeff_monomial, hh, hempty]

/-- Equality of the actual atom-mass polynomial and the source single-mode
polynomial. The statement has no supplied count-law or coefficient premise. -/
theorem finiteCountPolynomial_fourierBoundaryMeasure (d n : ℕ)
    (hd : 2 ≤ d) (hn : 0 < n) (origin x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    finiteCountPolynomial (fourierBoundaryMeasure d n) (boundaryArcCount d origin x) d =
      fourierCountPolynomial d n x := by
  letI : IsProbabilityMeasure (fourierBoundaryMeasure d n) :=
    fourierBoundaryMeasure_isProbabilityMeasure d n (by omega) hn
  apply Polynomial.funext
  intro z
  rw [finiteCountPolynomial_eval _ _ _ (measurable_boundaryArcCount d origin x)
    (boundaryArcCount_le d origin x)]
  rw [fourierBoundaryMeasure_count_generating d n hd hn origin x hx z]
  simp [fourierCountPolynomial, boundaryBinomialPolynomial, mul_assoc]

theorem fourierBoundaryMeasure_count_eq_coeff (d n h : ℕ)
    (hd : 2 ≤ d) (hn : 0 < n) (origin x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((fourierBoundaryMeasure d n).real {T | boundaryArcCount d origin x T = h} : ℂ) =
      (fourierCountPolynomial d n x).coeff h := by
  rw [← finiteCountPolynomial_fourierBoundaryMeasure d n hd hn origin x hx,
    finiteCountPolynomial_coeff _ _ _ _ (boundaryArcCount_le d origin x)]

end
end CGLMPBounds.Partition
