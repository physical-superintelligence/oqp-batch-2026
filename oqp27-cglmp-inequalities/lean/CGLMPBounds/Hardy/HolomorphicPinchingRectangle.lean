module

public import CGLMPBounds.Defs.HolomorphicPinching
public import CGLMPBounds.Hardy.PositivePinchingFiniteMeasure
public import CGLMPBounds.Hardy.SpectrumImaginaryBound

@[expose] public section


/-! The actual compact rectangle used in C.5. All norms below are Hilbert
operator norms. The numerical-range estimate applies to defective matrices;
no simultaneous diagonalization of B and Y is assumed. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Set
open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma hermitian_involution_mem_unitary {B : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) : B ∈ unitary (Matrix ι ι ℂ) := by
  have hBB : B * B = 1 := by simpa only [pow_two] using hB2
  apply Unitary.mem_iff.mpr
  simpa only [Matrix.star_eq_conjTranspose, hB.eq] using (And.intro hBB hBB)

lemma positivePinching_part_norm_le {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) :
    ‖positivePinchingPart B Y‖ ≤ ‖Y‖ := by
  have hu := hermitian_involution_mem_unitary hB hB2
  have hc : ‖B * Y * B‖ = ‖Y‖ := by
    rw [CStarRing.norm_mul_mem_unitary _ hu, CStarRing.norm_mem_unitary_mul _ hu]
  calc
    ‖positivePinchingPart B Y‖ = (1 / 2 : ℝ) * ‖Y + B * Y * B‖ := by
      rw [positivePinchingPart, norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖Y‖ + ‖B * Y * B‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖Y‖ := by rw [hc]; ring

lemma matrix_spectrum_real_imaginary_rectangle {H Y : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) {z : ℂ}
    (hz : z ∈ spectrum ℂ (H + Complex.I • Y)) :
    |z.re| ≤ ‖H‖ ∧ |z.im| ≤ ‖Y‖ := by
  have him : |z.im| ≤ ‖Y‖ := by
    simpa only [norm_smul, Complex.norm_I, one_mul] using
      matrix_spectrum_abs_im_le_norm_perturbation hH hz
  let u : ℂˣ := Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)
  have hz' : u • z ∈ spectrum ℂ (u • (H + Complex.I • Y)) :=
    spectrum.smul_mem_smul_iff.mpr hz
  have he : u • (H + Complex.I • Y) = Y + (-Complex.I) • H := by
    change (-Complex.I) • (H + Complex.I • Y) = _
    rw [smul_add, smul_smul]
    simp only [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    exact add_comm _ _
  rw [he] at hz'
  have hre := matrix_spectrum_abs_im_le_norm_perturbation hY hz'
  have hei : (u • z).im = -z.re := by
    change ((-Complex.I) * z).im = -z.re
    simp [Complex.mul_im]
  rw [hei, abs_neg, norm_smul, norm_neg, Complex.norm_I, one_mul] at hre
  exact ⟨hre, him⟩

theorem positivePinching_spectra_rectangle [Nonempty ι]
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ z ∈ spectrum ℂ ((ρ : ℂ) • B + Complex.I • Y),
      |z.re| ≤ ρ ∧ |z.im| ≤ ‖Y‖) ∧
    (∀ z ∈ spectrum ℂ ((ρ : ℂ) • B + Complex.I • positivePinchingPart B Y),
      |z.re| ≤ ρ ∧ |z.im| ≤ ‖Y‖) := by
  have hH : ((ρ : ℂ) • B).IsHermitian := hB.smul (by simp [isSelfAdjoint_iff])
  have hnorm : ‖(ρ : ℂ) • B‖ = ρ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ,
      CStarRing.norm_of_mem_unitary (hermitian_involution_mem_unitary hB hB2), mul_one]
  constructor
  · intro z hz
    simpa only [hnorm] using matrix_spectrum_real_imaginary_rectangle hH hY hz
  · intro z hz
    have hb := matrix_spectrum_real_imaginary_rectangle hH
      (positivePinching_part_hermitian hB hY) hz
    exact ⟨hnorm ▸ hb.1, hb.2.trans (positivePinching_part_norm_le hB hB2)⟩

lemma strip_argument_mem {ρ x y : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Icc (-1 : ℝ) 1) :
    -(ρ : ℂ) * x + Complex.I * y ∈ openVerticalUnitStrip := by
  change |(-(ρ : ℂ) * x + Complex.I * y).re| < 1
  have hx' : |x| ≤ 1 := abs_le.mpr hx
  have he : (-(ρ : ℂ) * x + Complex.I * y).re = -ρ * x := by
    simp [Complex.mul_re]
  rw [he, abs_mul, abs_neg, abs_of_nonneg hρ.1]
  calc
    ρ * |x| ≤ ρ * 1 := mul_le_mul_of_nonneg_left hx' hρ.1
    _ < 1 := by simpa only [mul_one] using hρ.2

end
end CGLMPBounds.Hardy
