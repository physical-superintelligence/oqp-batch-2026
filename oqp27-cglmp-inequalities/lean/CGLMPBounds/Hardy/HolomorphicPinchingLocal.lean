module

public import CGLMPBounds.Hardy.HolomorphicMomentDisk
public import CGLMPBounds.Hardy.HolomorphicPinchingParameterIntegral
public import CGLMPBounds.Hardy.PositivePinchingPolynomial
public import CGLMPBounds.Hardy.SpectralTracePolynomial

@[expose] public section


/-! Actual local C.10 identity for a function holomorphic on the source
strip. The matrix and scalar spectra fit a smaller disk for small complex
t. The generic moment premise is discharged by the proved polynomial
identity for the literal positive pinching measure. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix Polynomial Set Metric Filter MeasureTheory
open scoped Topology Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma pinching_affine_norm_le {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℂ) :
    ‖(ρ : ℂ) • B + t • Y‖ ≤ ρ + ‖t‖ * ‖Y‖ := by
  calc
    _ ≤ ‖(ρ : ℂ) • B‖ + ‖t • Y‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ,
        CStarRing.norm_of_mem_unitary (hermitian_involution_mem_unitary hB hB2), mul_one]

theorem positivePinching_holomorphic_local
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f openVerticalUnitStrip) :
    ∀ᶠ t : ℂ in 𝓝 0,
      normalizedSpectralTrace f ((ρ : ℂ) • B + t • Y) -
        normalizedSpectralTrace f ((ρ : ℂ) • B + t • positivePinchingPart B Y) =
        t ^ 2 * ∫ p : ℝ × ℝ, iteratedDeriv 2 f (-(ρ : ℂ) * p.1 + t * p.2)
          ∂positivePinchingMeasure B Y := by
  let M : ℝ := (ρ + 1) / 2
  let R : ℝ := (M + 1) / 2
  have hρM : ρ < M := by dsimp [M]; linarith [hρ.2]
  have hM : 0 < M := hρ.1.trans_lt hρM
  have hM1 : M < 1 := by dsimp [M]; linarith [hρ.2]
  have hMR : M < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hε : 0 < (M - ρ) / (‖Y‖ + 1) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
  have ht' : ‖t‖ < (M - ρ) / (‖Y‖ + 1) := by
    simpa only [mem_ball, dist_zero_right] using ht
  have hb : ρ + ‖t‖ * ‖Y‖ ≤ M := by
    have he := (lt_div_iff₀ (show 0 < ‖Y‖ + 1 by positivity)).mp ht'
    nlinarith [norm_nonneg t]
  let H : Matrix ι ι ℂ := (ρ : ℂ) • B + t • Y
  let C : Matrix ι ι ℂ := (ρ : ℂ) • B + t • positivePinchingPart B Y
  have hH : ‖H‖ ≤ M := (pinching_affine_norm_le hB hB2 hρ.1 t).trans hb
  have hC : ‖C‖ ≤ M := by
    apply (pinching_affine_norm_le hB hB2 hρ.1 t).trans
    exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (positivePinching_part_norm_le hB hB2) (norm_nonneg t))).trans hb
  have hroots (A : Matrix ι ι ℂ) (hA : ‖A‖ ≤ M) :
      ∀ a ∈ A.charpoly.roots, ‖a‖ ≤ M := by
    intro a ha
    exact (spectrum.norm_le_norm_of_mem (Matrix.mem_spectrum_of_isRoot_charpoly
      (Polynomial.isRoot_of_mem_roots ha))).trans hA
  let ν := positivePinchingMeasure B Y
  letI : IsFiniteMeasure ν := positivePinching_measure_finite hB hB2 hY
  let K : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ
    Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))
  let A : ℝ × ℝ → ℂ := fun p => -(ρ : ℂ) * p.1 + t * p.2
  have hA : Continuous A := by fun_prop
  let L : Set ℂ := A '' K
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hL : IsCompact L := hK.image hA
  have hLM : ∀ a ∈ L, ‖a‖ ≤ M := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := ha
    have hx : |p.1| ≤ 1 := abs_le.mpr hp.1
    have hy := hermitian_spectral_interval_abs_le_norm hY hp.2
    calc
      ‖A p‖ ≤ ‖-(ρ : ℂ) * p.1‖ + ‖t * p.2‖ := norm_add_le _ _
      _ = ρ * |p.1| + ‖t‖ * |p.2| := by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hρ.1]
      _ ≤ ρ + ‖t‖ * ‖Y‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hx hρ.1,
          mul_le_mul_of_nonneg_left hy (norm_nonneg t)]
      _ ≤ M := hb
  let μ : Measure ℂ := ν.map A
  have hνK : ∀ᵐ p ∂ν, p ∈ K := by
    apply ae_iff.mpr
    exact positivePinching_measure_outside_rectangle hB hB2 hY
  have hμL : ∀ᵐ a ∂μ, a ∈ L := by
    apply (ae_map_iff hA.measurable.aemeasurable hL.measurableSet).mpr
    exact hνK.mono fun p hp => mem_image_of_mem A hp
  have hrestrict : μ.restrict L = μ := Measure.restrict_eq_self_of_ae_mem hμL
  have hmap (g : ℂ → ℂ) (hg : ContinuousOn g L) :
      (∫ a in L, g a ∂μ) = ∫ p : ℝ × ℝ, g (A p) ∂ν := by
    have hm : AEStronglyMeasurable g μ := by
      simpa only [hrestrict] using hg.aestronglyMeasurable (μ := μ) hL.measurableSet
    rw [hrestrict]
    exact integral_map hA.measurable.aemeasurable hm
  have hmom : ∀ n : ℕ,
      (H.charpoly.roots.map (fun a => a ^ n)).sum / (Fintype.card ι : ℂ) -
        (C.charpoly.roots.map (fun a => a ^ n)).sum / (Fintype.card ι : ℂ) =
          t ^ 2 * (∫ a in L, (X ^ n : ℂ[X]).derivative.derivative.eval a ∂μ) := by
    intro n
    rw [hmap _ (by fun_prop)]
    have hp := positivePinching_polynomial_identity hB hB2 hY (X ^ n) (ρ : ℂ) t
    rw [← normalizedSpectralTrace_polynomial, ← normalizedSpectralTrace_polynomial] at hp
    simpa only [normalizedSpectralTrace, Polynomial.eval_pow, Polynomial.eval_X, ν, A, H, C] using hp
  have hball : closedBall (0 : ℂ) R ⊆ openVerticalUnitStrip := by
    intro z hz
    exact (Complex.abs_re_le_norm z).trans_lt
      ((by simpa only [mem_closedBall, dist_zero_right] using hz : ‖z‖ ≤ R).trans_lt hR1)
  have he := holomorphic_identity_of_polynomial_moments H.charpoly.roots C.charpoly.roots
    (Fintype.card ι : ℂ) (t ^ 2) hL μ hM hMR (hroots H hH) (hroots C hC) hLM hmom
    (hf.mono hball)
  have hderiv : ContinuousOn (iteratedDeriv 2 f) L := by
    rw [iteratedDeriv_eq_iterate]
    exact (hf.iterated_deriv 2).continuousOn.mono (fun a ha =>
      hball (by simpa only [mem_closedBall, dist_zero_right] using (hLM a ha).trans hMR.le))
  rw [hmap _ hderiv] at he
  exact he

end
end CGLMPBounds.Hardy
