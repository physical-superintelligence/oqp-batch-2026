module

public import CGLMPBounds.Partition.MixtureIntegrals
public import CGLMPBounds.Partition.BinomialLaw

@[expose] public section


/-! The actual count law under a positive summable Fourier mixture.
This structural theorem isolates precisely the still-open source obligation:
identify the particular v from (D.5) with a mixtureShape of positive summable
coefficients of mass π/4−1/2. No such identification is assumed implicitly. -/

namespace CGLMPBounds.Partition
open MeasureTheory
noncomputable section

lemma fourierTiltShape_nonneg (n : ℕ) (x : ℝ) : 0 ≤ fourierTiltShape n x := by
  exact div_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma fourierTiltShape_succ_le_one (n : ℕ) (x : ℝ) :
    fourierTiltShape (n + 1) x ≤ 1 := by
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hp : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hn2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hden : (1 : ℝ) ≤ Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hn2)]
  unfold fourierTiltShape
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr
  simpa only [one_mul] using (Real.sin_sq_le_one _).trans hden

lemma summable_weighted_fourierTiltShape (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a) (x : ℝ) :
    Summable (fun n => a n * fourierTiltShape (n + 1) x) := by
  apply ha.of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (mul_nonneg (ha0 n) (fourierTiltShape_nonneg _ _))]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (fourierTiltShape_succ_le_one n x) (ha0 n)

theorem fourierMixtureMeasure_count_law (d h : ℕ) (hd : 2 ≤ d)
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (ha : Summable a)
    (hmass : (∑' n, a n) ≤ 1) (origin x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (fourierMixtureMeasure d a).real {T | boundaryArcCount d origin x T = h} =
      scalarBinomialWeight d h x + fourierMixtureShape a x / d *
        iteratedDeriv 2 (scalarBinomialWeight d h) x := by
  have hE : MeasurableSet {T | boundaryArcCount d origin x T = h} :=
    (measurable_boundaryArcCount d origin x) (measurableSet_singleton h)
  rw [fourierMixtureMeasure_real d a ha0 ha hmass _ hE,
    boundaryArcCount_binomial d h origin x hx]
  simp_rw [fourierBoundaryMeasure_count_law d _ h hd (Nat.succ_pos _) origin x hx]
  let P := scalarBinomialWeight d h x
  let D := iteratedDeriv 2 (scalarBinomialWeight d h) x
  have hsplit : (fun n => a n * (P + fourierTiltShape (n + 1) x / d * D)) =
      (fun n => a n * P + (a n * fourierTiltShape (n + 1) x) * (D / d)) := by
    funext n
    ring
  change fourierMixtureResidual a * P +
    (∑' n, a n * (P + fourierTiltShape (n + 1) x / d * D)) =
      P + fourierMixtureShape a x / d * D
  rw [hsplit, (ha.mul_right P).tsum_add
      ((summable_weighted_fourierTiltShape a ha0 ha x).mul_right (D / d)),
    tsum_mul_right, tsum_mul_right]
  unfold fourierMixtureResidual fourierMixtureShape
  ring

end
end CGLMPBounds.Partition
