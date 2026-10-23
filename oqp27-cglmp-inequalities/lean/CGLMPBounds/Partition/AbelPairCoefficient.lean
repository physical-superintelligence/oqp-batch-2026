module

public import CGLMPBounds.Partition.AbelPairIntegralLimit

@[expose] public section


/-! The actual pair of cell Fourier coefficients equals the complex
double integral. Geometric damping permits an honest sum/integral
exchange by summability of integral norms. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
noncomputable section

lemma scalar_interval_fourier_pair {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (α : ℝ) :
    star (∫ s in a..b, Complex.exp ((((α * s : ℝ) : ℂ)) * Complex.I)) *
      (∫ t in c..d, Complex.exp ((((α * t : ℝ) : ℂ)) * Complex.I)) =
      ∫ p : ℝ × ℝ, Complex.exp ((((α * (p.2 - p.1) : ℝ) : ℂ)) * Complex.I)
        ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    Complex.star_def, ← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem quarterBranchAbelKernel_coefficient_series_hasSum
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n : ℕ => (q : ℂ) ^ n *
      (star (∫ s in a..b,
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * s : ℝ) : ℂ)) * Complex.I)) *
       (∫ t in c..d,
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I))))
      (∫ p : ℝ × ℝ, quarterBranchAbelKernel q (p.2 - p.1)
        ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)))) := by
  let μ : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))
  let F : ℕ → (ℝ × ℝ) → ℂ := fun n p => (q : ℂ) ^ n *
    Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) *
      (p.2 - p.1) : ℝ) : ℂ)) * Complex.I)
  have hnorm (n : ℕ) (p : ℝ × ℝ) : ‖F n p‖ = q ^ n := by
    simp only [F, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq₀, mul_one]
  have hi (n : ℕ) : Integrable (F n) μ := by
    apply (integrable_const (q ^ n : ℝ)).mono'
      (by dsimp [F]; fun_prop : Measurable (F n)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => (hnorm n p).le)
  have hs : Summable (fun n : ℕ => ∫ p, ‖F n p‖ ∂μ) := by
    have hg : Summable (fun n : ℕ => q ^ n) :=
      summable_geometric_of_norm_lt_one (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hq₀] using hq₁)
    simp_rw [hnorm, integral_const, smul_eq_mul]
    exact hg.mul_left _
  have he (n : ℕ) : (q : ℂ) ^ n *
      (star (∫ s in a..b,
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * s : ℝ) : ℂ)) * Complex.I)) *
       (∫ t in c..d,
        Complex.exp (((( (2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * t : ℝ) : ℂ)) * Complex.I))) =
      ∫ p, F n p ∂μ := by
    rw [scalar_interval_fourier_pair hab hcd]
    exact (integral_const_mul _ _).symm
  simp_rw [he]
  exact hasSum_integral_of_summable_integral_norm hi hs

end
end CGLMPBounds.Partition
