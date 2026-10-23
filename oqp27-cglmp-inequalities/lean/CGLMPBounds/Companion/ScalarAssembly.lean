module

public import CGLMPBounds.Companion.WeightedPairing

@[expose] public section


/-!
# Finite scalar assembly of the companion edge cost

The diagonal and paired off-diagonal Fourier kernels are assembled here. The
input is a Hermitian correlation array with unit diagonal on the finite range;
the matrix construction must supply these properties and identify its trace
expansion with this sum before the full companion Bell identity can be claimed.
-/

namespace CGLMPBounds.Companion
noncomputable section
open Finset

/-- The weighted residue kernel multiplying `z_kj` in the Fourier trace expansion. -/
def weightedKernel (d j k : ℕ) : ℂ :=
  (etaD d ^ j * (etaD d)⁻¹ ^ k) *
    ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r

/-- The source secant/cosecant term for one ordered frequency pair. -/
def pairedCorrelation (d j k : ℕ) (z : ℂ) : ℝ :=
  z.re / Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d)) -
    z.im / Real.sin (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d))

lemma weightedKernel_diagonal (d j : ℕ) :
    weightedKernel d j j = (d : ℂ) * ((d : ℂ) - 1) / 2 :=
  fourier_diag d j

lemma weightedKernel_pair {d j k : ℕ} (hjk : j < k) (hkd : k < d) (z : ℂ) :
    weightedKernel d j k * star z + weightedKernel d k j * z =
      (((-(d : ℝ) / 2) * pairedCorrelation d j k z : ℝ) : ℂ) := by
  rw [weightedKernel, weightedKernel, weighted_fourier_pair hjk hkd z]
  simp only [pairedCorrelation]
  push_cast
  ring

/-- Exact finite sum of all diagonal and oriented frequency-pair contributions. -/
theorem weightedKernel_sum (d : ℕ) (z : ℕ → ℕ → ℂ)
    (hdiag : ∀ j, j < d → z j j = 1)
    (hstar : ∀ j k, j < k → k < d → z k j = star (z j k)) :
    (∑ j ∈ range d, ∑ k ∈ range d, weightedKernel d j k * z k j) =
      (((d : ℝ) ^ 2 * ((d : ℝ) - 1) / 2 -
        (d : ℝ) / 2 * ∑ k ∈ range d, ∑ j ∈ range k,
          pairedCorrelation d j k (z j k) : ℝ) : ℂ) := by
  rw [sum_range_sum_range_eq]
  have hD : (∑ j ∈ range d, weightedKernel d j j * z j j) =
      (((d : ℝ) ^ 2 * ((d : ℝ) - 1) / 2 : ℝ) : ℂ) := by
    have ht : ∀ j ∈ range d, weightedKernel d j j * z j j =
        (d : ℂ) * ((d : ℂ) - 1) / 2 := by
      intro j hj
      rw [hdiag j (mem_range.mp hj), mul_one, weightedKernel_diagonal]
    rw [Finset.sum_congr rfl ht, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hO : (∑ k ∈ range d, ∑ j ∈ range k,
        (weightedKernel d j k * z k j + weightedKernel d k j * z j k)) =
      (((-(d : ℝ) / 2) * ∑ k ∈ range d, ∑ j ∈ range k,
        pairedCorrelation d j k (z j k) : ℝ) : ℂ) := by
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := mem_range.mp hj
    have hkd := mem_range.mp hk
    rw [hstar j k hjk hkd]
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.ofReal_ofNat] using weightedKernel_pair hjk hkd (z j k)
  rw [hD, hO]
  push_cast
  ring

/-- After physical and multiplicity trace normalization, the source's one-edge formula. -/
theorem normalized_weightedKernel_sum (d : ℕ) (hd : d ≠ 0) (z : ℕ → ℕ → ℂ)
    (hdiag : ∀ j, j < d → z j j = 1)
    (hstar : ∀ j k, j < k → k < d → z k j = star (z j k)) :
    ((∑ j ∈ range d, ∑ k ∈ range d, weightedKernel d j k * z k j) / (d : ℂ) ^ 2) =
      ((((d : ℝ) - 1) / 2 - (1 / (2 * (d : ℝ))) *
        ∑ k ∈ range d, ∑ j ∈ range k, pairedCorrelation d j k (z j k) : ℝ) : ℂ) := by
  rw [weightedKernel_sum d z hdiag hstar]
  push_cast
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  field_simp [hdC] <;> ring

end
end CGLMPBounds.Companion
