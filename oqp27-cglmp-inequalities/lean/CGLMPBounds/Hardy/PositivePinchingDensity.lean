module

public import CGLMPBounds.Hardy.PositivePinchingAlgebra
public import CGLMPBounds.Hardy.DensityIntegrability

@[expose] public section


/-! The literal C.4 density: nonnegativity, joint measurability, actual spectral
rectangle support and integrability in the y variable. Joint integrability and
the uniform x majorant are separate obligations; no Fubini premise is hidden. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positivePinching_omega_nonneg (B Y : Matrix ι ι ℂ) (x y : ℝ) :
    0 ≤ positivePinchingOmega B Y x y := by
  apply div_nonneg
  · apply Multiset.sum_nonneg
    intro t ht
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp ht
    exact abs_nonneg _
  · positivity

theorem positivePinching_density_nonneg (B Y : Matrix ι ι ℂ) (p : ℝ × ℝ) :
    0 ≤ positivePinchingDensity B Y p := by
  unfold positivePinchingDensity
  split_ifs with hp
  · exact div_nonneg (positivePinching_omega_nonneg B Y p.1 p.2)
      (positivePinching_strip_denominator_pos hp).le
  · exact le_rfl

theorem continuous_positivePinchingOmega (B Y : Matrix ι ι ℂ) :
    Continuous (fun p : ℝ × ℝ => positivePinchingOmega B Y p.1 p.2) := by
  have hp : Continuous (fun p : ℝ × ℝ =>
      (B - (p.1 : ℂ) • (1 : Matrix ι ι ℂ)) *
        (Y - (p.2 : ℂ) • (1 : Matrix ι ι ℂ))) := by fun_prop
  have hf : Continuous (fun z : ℂ => |z.im|) := by fun_prop
  exact ((continuous_charpoly_root_sum (ι := ι) (fun z : ℂ => |z.im|) hf).comp hp).div_const (2 * Real.pi * Fintype.card ι)

theorem measurable_positivePinchingDensity (B Y : Matrix ι ι ℂ) :
    Measurable (positivePinchingDensity B Y) := by
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Set.Ioo (-1 : ℝ) 1} :=
    measurableSet_Ioo.preimage measurable_fst
  have hq : Measurable (fun p : ℝ × ℝ =>
      positivePinchingOmega B Y p.1 p.2 / (1 - p.1 ^ 2)) :=
    (continuous_positivePinchingOmega B Y).measurable.div
      (measurable_const.sub (measurable_fst.pow_const 2))
  exact Measurable.ite hs hq measurable_const

theorem positivePinching_omega_eq_zero_outside_spectralInterval
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {x y : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∉ Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y))) :
    positivePinchingOmega B Y x y = 0 := by
  rw [positivePinching_omega_eq_traceDensity hB2 hx]
  exact traceDensity_eq_zero_outside_spectralInterval
    (positivePinching_shift_hermitian hB x).inv hY
    (Matrix.isUnit_nonsing_inv_det _ (positivePinching_shift_isUnit_det hB2 hx)) hy

theorem positivePinching_density_eq_zero_outside_rectangle
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {p : ℝ × ℝ}
    (hp : p ∉ (Set.Icc (-1 : ℝ) 1 ×ˢ
      Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)))) :
    positivePinchingDensity B Y p = 0 := by
  unfold positivePinchingDensity
  split_ifs with hx
  · have hy : p.2 ∉ Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)) := by
      intro hy
      exact hp ⟨⟨hx.1.le, hx.2.le⟩, hy⟩
    rw [positivePinching_omega_eq_zero_outside_spectralInterval hB hB2 hY hx hy,
      zero_div]
  · rfl

theorem positivePinching_measure_outside_rectangle
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) :
    positivePinchingMeasure B Y
      ((Set.Icc (-1 : ℝ) 1 ×ˢ
        Set.Icc (sInf (spectrum ℝ Y)) (sSup (spectrum ℝ Y)))ᶜ) = 0 := by
  rw [positivePinchingMeasure, withDensity_apply _
    ((measurableSet_Icc.prod measurableSet_Icc).compl)]
  apply setLIntegral_eq_zero ((measurableSet_Icc.prod measurableSet_Icc).compl)
  intro p hp
  change ENNReal.ofReal (positivePinchingDensity B Y p) = 0
  rw [positivePinching_density_eq_zero_outside_rectangle hB hB2 hY hp,
    ENNReal.ofReal_zero]

theorem positivePinching_omega_moment_integrable
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (m : ℕ) :
    Integrable (fun y : ℝ => y ^ m * positivePinchingOmega B Y x y) volume := by
  simp_rw [positivePinching_omega_eq_traceDensity hB2 hx]
  exact traceDensity_moment_integrable
    (positivePinching_shift_hermitian hB x).inv hY
    (Matrix.isUnit_nonsing_inv_det _ (positivePinching_shift_isUnit_det hB2 hx)) m

theorem positivePinching_density_slice_moment_integrable
    {B Y : Matrix ι ι ℂ} (hB : B.IsHermitian) (hB2 : B ^ 2 = 1)
    (hY : Y.IsHermitian) (x : ℝ) (m : ℕ) :
    Integrable (fun y : ℝ => y ^ m * positivePinchingDensity B Y (x, y)) volume := by
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · simp only [positivePinchingDensity, hx, if_pos, mul_div_assoc]
    simpa only [mul_div_assoc] using
      (positivePinching_omega_moment_integrable hB hB2 hY hx m).div_const (1 - x ^ 2)
  · have hzero : (fun y : ℝ => y ^ m * positivePinchingDensity B Y (x, y)) =
        (0 : ℝ → ℝ) := by
      funext y
      simp only [positivePinchingDensity, hx, ite_false, mul_zero, Pi.zero_apply]
    rw [hzero]
    exact integrable_zero ℝ ℝ volume

end
end CGLMPBounds.Hardy
