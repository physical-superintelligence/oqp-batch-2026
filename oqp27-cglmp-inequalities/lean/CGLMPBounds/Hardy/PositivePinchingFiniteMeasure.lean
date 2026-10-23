module

public import CGLMPBounds.Hardy.PositivePinchingMajorant

@[expose] public section


/-! Joint integrability and actual finiteness of the C.4 measure. The majorant
is the product of the integrable arcsine weight and the indicator of Y's finite
spectral interval. This supplies the Fubini premises rather than assuming them. -/

open scoped Polynomial

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem positivePinching_density_integrable {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) (hY : Y.IsHermitian) :
    Integrable (positivePinchingDensity B Y) volume := by
  let f : ℝ → ℝ := (Ioo (-1 : ℝ) 1).indicator
    (fun x => (Real.sqrt (1 - x ^ 2))⁻¹)
  let g : ℝ → ℝ := (Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))).indicator
    (fun _ => (1 : ℝ))
  have hf : Integrable f volume := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
    simpa only [Real.sqrt_inv] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have hg : Integrable g volume := by
    exact (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator
      measurableSet_Icc
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      (‖positivePinchingOffdiag B Y‖ / (2 * Real.pi)) * (f p.1 * g p.2)) volume :=
    (hf.mul_prod hg).const_mul _
  apply hmajor.mono' (measurable_positivePinchingDensity B Y).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (positivePinching_density_nonneg B Y p)]
  by_cases hx : p.1 ∈ Ioo (-1 : ℝ) 1
  · by_cases hy : p.2 ∈ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))
    · simp only [f, g, Set.indicator_of_mem hx, Set.indicator_of_mem hy, mul_one]
      simpa only [div_eq_mul_inv, _root_.mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
        positivePinching_density_le_majorant hB hB2 hY hx p.2
    · have hzero : positivePinchingDensity B Y p = 0 :=
        positivePinching_density_eq_zero_outside_rectangle hB hB2 hY
          (fun hp => hy hp.2)
      simp only [g, Set.indicator_of_notMem hy, mul_zero, hzero, le_refl]
  · simp [positivePinchingDensity, hx, f]

theorem positivePinching_measure_finite {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) (hY : Y.IsHermitian) :
    IsFiniteMeasure (positivePinchingMeasure B Y) :=
  isFiniteMeasure_withDensity_ofReal (positivePinching_density_integrable hB hB2 hY).2

theorem positivePinching_continuous_integrable {B Y : Matrix ι ι ℂ}
    (hB : B.IsHermitian) (hB2 : B ^ 2 = 1) (hY : Y.IsHermitian)
    {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    Integrable f (positivePinchingMeasure B Y) := by
  letI := positivePinching_measure_finite hB hB2 hY
  let K := Icc (-1 : ℝ) 1 ×ˢ Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))
  have hin : IntegrableOn f K (positivePinchingMeasure B Y) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hout : IntegrableOn f Kᶜ (positivePinchingMeasure B Y) := by
    have hz : (positivePinchingMeasure B Y).restrict Kᶜ = 0 :=
      Measure.restrict_eq_zero.mpr (positivePinching_measure_outside_rectangle hB hB2 hY)
    simp only [IntegrableOn, hz, integrable_zero_measure]
  simpa only [Set.union_compl_self, integrableOn_univ] using hin.union hout

theorem positivePinching_polynomial_second_derivative_integrable
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (f : ℂ[X]) (s t : ℂ) :
    Integrable (fun p : ℝ × ℝ => f.derivative.derivative.eval (-s * p.1 + t * p.2))
      (positivePinchingMeasure B Y) := by
  apply positivePinching_continuous_integrable hB hB2 hY
  fun_prop

end
end CGLMPBounds.Hardy
