module

public import CGLMPBounds.Hardy.HolomorphicPinchingRectangle
public import CGLMPBounds.Hardy.HolomorphicTraceAnalytic

@[expose] public section


/-! A genuine connected parameter domain for the C.5 continuation. The
vertical strip |Re t| < (1-ρ)/(‖Y‖+1) contains both 0 and i. Numerical-range
bounds keep both matrix spectra and all scalar support arguments in the
source strip, without requiring a disk to enclose its full vertical extent. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Set
open scoped Matrix.Norms.Operator in
private lemma analyticAt_affine_matrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : Matrix κ κ ℂ) (z : ℂ) : AnalyticAt ℂ (fun w => A + w • B) z := by
  apply AnalyticAt.fun_add
  · exact analyticAt_const
  · apply AnalyticAt.fun_smul
    · exact analyticAt_id
    · exact analyticAt_const

open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma hermitian_spectral_interval_abs_le_norm {Y : Matrix ι ι ℂ}
    (hY : Y.IsHermitian) {y : ℝ}
    (hy : y ∈ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))) : |y| ≤ ‖Y‖ := by
  have hn : (spectrum ℝ Y).Nonempty := by
    rw [hY.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _
  have hb : ∀ a ∈ spectrum ℝ Y, |a| ≤ ‖Y‖ := by
    intro a ha
    simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem ha
  have hlow : -‖Y‖ ≤ sInf (spectrum ℝ Y) :=
    le_csInf hn (fun a ha => (abs_le.mp (hb a ha)).1)
  have hhigh : sSup (spectrum ℝ Y) ≤ ‖Y‖ :=
    csSup_le hn (fun a ha => (abs_le.mp (hb a ha)).2)
  exact abs_le.mpr ⟨hlow.trans hy.1, hy.2.trans hhigh⟩

lemma pinching_parameter_margin {ρ N : ℝ} (hN : 0 ≤ N) {t : ℂ}
    (ht : |t.re| < (1 - ρ) / (N + 1)) : ρ + |t.re| * N < 1 := by
  have hp : 0 < N + 1 := by linarith
  have he := (lt_div_iff₀ hp).mp ht
  nlinarith [abs_nonneg t.re]

theorem positivePinching_parameter_scalar_mem_strip
    {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) {ρ : ℝ} (hρ : 0 ≤ ρ) {t : ℂ}
    (ht : |t.re| < (1 - ρ) / (‖Y‖ + 1)) {p : ℝ × ℝ}
    (hp : p ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))) :
    -(ρ : ℂ) * p.1 + t * p.2 ∈ openVerticalUnitStrip := by
  have hx : |p.1| ≤ 1 := abs_le.mpr hp.1
  have hy := hermitian_spectral_interval_abs_le_norm hY hp.2
  have he : (-(ρ : ℂ) * p.1 + t * p.2).re = -ρ * p.1 + t.re * p.2 := by
    simp [Complex.mul_re]
  change |(-(ρ : ℂ) * p.1 + t * p.2).re| < 1
  rw [he]
  calc
    |-ρ * p.1 + t.re * p.2| ≤ |-ρ * p.1| + |t.re * p.2| := abs_add_le _ _
    _ = ρ * |p.1| + |t.re| * |p.2| := by rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hρ]
    _ ≤ ρ + |t.re| * ‖Y‖ := by
      nlinarith [mul_le_mul_of_nonneg_left hx hρ,
        mul_le_mul_of_nonneg_left hy (abs_nonneg t.re)]
    _ < 1 := pinching_parameter_margin (norm_nonneg Y) ht

lemma complex_parameter_matrix_decomposition (B Y : Matrix ι ι ℂ) (ρ : ℝ) (t : ℂ) :
    (ρ : ℂ) • B + t • Y =
      ((ρ : ℂ) • B + (t.re : ℂ) • Y) + Complex.I • ((t.im : ℂ) • Y) := by
  have ht : (t.re : ℂ) + Complex.I * (t.im : ℂ) = t := by
    simpa only [mul_comm] using Complex.re_add_im t
  rw [smul_smul, add_assoc, ← add_smul, ht]

lemma hermitian_parameter_real_spectrum_bound {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) (hY : Y.IsHermitian)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ ((ρ : ℂ) • B + t • Y)) :
    |z.re| ≤ ρ + |t.re| * ‖Y‖ := by
  have hH : ((ρ : ℂ) • B + (t.re : ℂ) • Y).IsHermitian :=
    (hB.smul (by simp [isSelfAdjoint_iff])).add (hY.smul (by simp [isSelfAdjoint_iff]))
  have hD : ((t.im : ℂ) • Y).IsHermitian := hY.smul (by simp [isSelfAdjoint_iff])
  rw [complex_parameter_matrix_decomposition] at hz
  have hbound := (matrix_spectrum_real_imaginary_rectangle hH hD hz).1
  have hnB : ‖(ρ : ℂ) • B‖ = ρ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ,
      CStarRing.norm_of_mem_unitary (hermitian_involution_mem_unitary hB hB2), mul_one]
  apply hbound.trans
  calc
    ‖(ρ : ℂ) • B + (t.re : ℂ) • Y‖ ≤ ‖(ρ : ℂ) • B‖ + ‖(t.re : ℂ) • Y‖ := norm_add_le _ _
    _ = ρ + |t.re| * ‖Y‖ := by rw [hnB, norm_smul, Complex.norm_real, Real.norm_eq_abs]

theorem positivePinching_parameter_spectra_mem_strip
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {ρ : ℝ} (hρ : 0 ≤ ρ) {t : ℂ}
    (ht : |t.re| < (1 - ρ) / (‖Y‖ + 1)) :
    spectrum ℂ ((ρ : ℂ) • B + t • Y) ⊆ openVerticalUnitStrip ∧
      spectrum ℂ ((ρ : ℂ) • B + t • positivePinchingPart B Y) ⊆ openVerticalUnitStrip := by
  have hm := pinching_parameter_margin (norm_nonneg Y) ht
  constructor
  · intro z hz
    exact (hermitian_parameter_real_spectrum_bound hB hB2 hY hρ t hz).trans_lt hm
  · intro z hz
    have hb := hermitian_parameter_real_spectrum_bound hB hB2
      (positivePinching_part_hermitian hB hY) hρ t hz
    apply hb.trans_lt
    exact lt_of_le_of_lt (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (positivePinching_part_norm_le hB hB2) (abs_nonneg t.re))) hm

theorem analyticOnNhd_positivePinching_parameter_trace
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {ρ : ℝ} (hρ : 0 ≤ ρ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f openVerticalUnitStrip) :
    AnalyticOnNhd ℂ (fun t => normalizedSpectralTrace f ((ρ : ℂ) • B + t • Y) -
      normalizedSpectralTrace f ((ρ : ℂ) • B + t • positivePinchingPart B Y))
      {t : ℂ | |t.re| < (1 - ρ) / (‖Y‖ + 1)} := by
  have hS : IsOpen openVerticalUnitStrip := isOpen_lt Complex.continuous_re.abs continuous_const
  intro t ht
  have hs := positivePinching_parameter_spectra_mem_strip hB hB2 hY hρ ht
  exact (analyticAt_normalizedSpectralTrace hS
    (analyticAt_affine_matrix ((ρ : ℂ) • B) Y t) hf hs.1).sub
    (analyticAt_normalizedSpectralTrace hS
      (analyticAt_affine_matrix ((ρ : ℂ) • B) (positivePinchingPart B Y) t) hf hs.2)

end
end CGLMPBounds.Hardy
