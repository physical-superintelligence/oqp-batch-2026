module

public import CGLMPBounds.Defs.CircularPoisson
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section


/-! Actual circle Herglotz kernel: its uniformly summable geometric
expansion, normalized mean, and quantitative positive Poisson lower bound. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ComplexConjugate
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

lemma circle_fourier_norm (k : ℤ) (t : UnitCircle) : ‖fourier k t‖ = 1 :=
  Circle.norm_coe _

lemma circle_fourier_ne_zero (k : ℤ) (t : UnitCircle) : fourier k t ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [circle_fourier_norm]; norm_num)

lemma circle_fourier_nat_pow (n : ℕ) (t : UnitCircle) :
    fourier 1 t ^ n = fourier (n : ℤ) t := by
  induction n with
  | zero => simp [fourier_zero]
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, fourier_add]

lemma circle_integral_fourier (k : ℤ) :
    (∫ t : UnitCircle, fourier k t ∂circleMeasure) = if k=0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) k) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul,
    Pi.single_apply, eq_comm] using h

lemma circleHerglotz_denominator_ne {z : ℂ} (hz : ‖z‖ < 1) (t : UnitCircle) :
    fourier 1 t - z ≠ 0 := by
  intro he
  have h := congrArg norm (sub_eq_zero.mp he)
  rw [circle_fourier_norm] at h
  linarith

lemma continuous_circleHerglotzKernel {z : ℂ} (hz : ‖z‖ < 1) :
    Continuous (circleHerglotzKernel z) := by
  exact ((fourier 1).continuous.add continuous_const).div
    ((fourier 1).continuous.sub continuous_const) (circleHerglotz_denominator_ne hz)

lemma circleHerglotzKernel_hasSum {z : ℂ} (hz : ‖z‖ < 1) (t : UnitCircle) :
    HasSum (fun n : ℕ => (z / fourier 1 t)^(n+1))
      ((circleHerglotzKernel z t - 1)/2) := by
  have hratio : ‖z/fourier 1 t‖ < 1 := by simpa [norm_div,circle_fourier_norm] using hz
  have h := (hasSum_geometric_of_norm_lt_one hratio).mul_right (z/fourier 1 t)
  convert h using 1
  · ext n
    rw [pow_succ]
  · unfold circleHerglotzKernel
    rw [one_sub_div (circle_fourier_ne_zero 1 t), inv_div]
    have hden := mul_inv_cancel₀ (circleHerglotz_denominator_ne hz t)
    field_simp [circle_fourier_ne_zero 1 t, circleHerglotz_denominator_ne hz t]
    linear_combination hden

lemma circleHerglotzKernel_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) (t : UnitCircle) :
    circleHerglotzKernel z t = 1 + 2 * ∑' n : ℕ, (z/fourier 1 t)^(n+1) := by
  rw [(circleHerglotzKernel_hasSum hz t).tsum_eq]
  ring

lemma circle_geometric_term_eq (z : ℂ) (n : ℕ) (t : UnitCircle) :
    (z/fourier 1 t)^(n+1) = z^(n+1)*fourier (-((n+1 : ℕ) : ℤ)) t := by
  rw [div_pow, circle_fourier_nat_pow, fourier_neg]
  have hunit : fourier ((n+1 : ℕ) : ℤ) t * conj (fourier ((n+1 : ℕ) : ℤ) t) = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, circle_fourier_norm]
    norm_num
  apply (div_eq_iff (circle_fourier_ne_zero ((n+1 : ℕ) : ℤ) t)).mpr
  rw [mul_assoc (z^(n+1)),
    mul_comm (conj (fourier ((n+1 : ℕ) : ℤ) t)) (fourier ((n+1 : ℕ) : ℤ) t),
    hunit, mul_one]

lemma circleHerglotzKernel_integral {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ t, circleHerglotzKernel z t ∂circleMeasure) = 1 := by
  have hterm (n : ℕ) : Integrable
      (fun t : UnitCircle => (z/fourier 1 t)^(n+1)) circleMeasure := by
    have hc : Continuous (fun t : UnitCircle => (z/fourier 1 t)^(n+1)) :=
      (continuous_const.div (fourier 1).continuous (circle_fourier_ne_zero 1)).pow (n+1)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : Summable (fun n : ℕ => ∫ t : UnitCircle,
      ‖(z/fourier 1 t)^(n+1)‖ ∂circleMeasure) := by
    simpa only [norm_pow,norm_div,circle_fourier_norm,div_one,integral_const,
      measure_univ,probReal_univ,ENNReal.toReal_one,one_smul] using
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg z) hz)
  have hi := integral_tsum_of_summable_integral_norm hterm hsum
  have hzero (n : ℕ) : (∫ t : UnitCircle, (z/fourier 1 t)^(n+1) ∂circleMeasure)=0 := by
    simp_rw [circle_geometric_term_eq]
    rw [integral_const_mul,circle_integral_fourier,if_neg (by omega),mul_zero]
  have hsumint : Integrable (fun t : UnitCircle => ∑' n : ℕ,
      (z/fourier 1 t)^(n+1)) circleMeasure := by
    have hc : Continuous (fun t : UnitCircle => (circleHerglotzKernel z t-1)/2) :=
      ((continuous_circleHerglotzKernel hz).sub continuous_const).div_const 2
    have he : (fun t : UnitCircle => ∑' n : ℕ,(z/fourier 1 t)^(n+1)) =
        (fun t => (circleHerglotzKernel z t-1)/2) :=
      funext (fun t => (circleHerglotzKernel_hasSum hz t).tsum_eq)
    rw [he]
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [circleHerglotzKernel_eq_tsum hz]
  rw [integral_add (integrable_const _) (hsumint.const_mul _),integral_const_mul,← hi]
  simp only [hzero,tsum_zero,mul_zero,add_zero,integral_const,measure_univ,
    probReal_univ,ENNReal.toReal_one,one_smul]

lemma circlePoissonKernel_formula (z : ℂ) (t : UnitCircle) :
    circlePoissonKernel z t = (1-‖z‖^2)/‖fourier 1 t-z‖^2 := by
  have h := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z))
    (fourier 1 t)
  simpa only [poissonKernel_def,herglotzRieszKernel_def,Function.comp_apply,
    sub_zero,circle_fourier_norm,one_pow,circlePoissonKernel,circleHerglotzKernel] using h.symm

theorem circlePoissonKernel_continuous {z : ℂ} (hz : ‖z‖ < 1) :
    Continuous (circlePoissonKernel z) :=
  Complex.continuous_re.comp (continuous_circleHerglotzKernel hz)

theorem circlePoissonKernel_integral {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ t, circlePoissonKernel z t ∂circleMeasure) = 1 := by
  change (∫ t, (circleHerglotzKernel z t).re ∂circleMeasure) = 1
  have h := integral_re (μ := circleMeasure)
    ((continuous_circleHerglotzKernel hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  rw [circleHerglotzKernel_integral hz] at h
  simpa only [RCLike.re_eq_complex_re, Complex.one_re] using! h

theorem circlePoissonKernel_lower {z : ℂ} (hz : ‖z‖ < 1) (t : UnitCircle) :
    (1-‖z‖)/(1+‖z‖) ≤ circlePoissonKernel z t := by
  rw [circlePoissonKernel_formula]
  have hd : 0 < ‖fourier 1 t-z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (circleHerglotz_denominator_ne hz t))
  have hu : ‖fourier 1 t-z‖ ≤ 1+‖z‖ := by
    simpa only [circle_fourier_norm] using norm_sub_le (fourier 1 t) z
  have hn : 0 ≤ 1-‖z‖^2 := by nlinarith [norm_nonneg z]
  calc
    (1-‖z‖)/(1+‖z‖) = (1-‖z‖^2)/(1+‖z‖)^2 := by
      field_simp [show (1+‖z‖) ≠ 0 by positivity]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left hn hd (by nlinarith [norm_nonneg (fourier 1 t-z)])

end
end CGLMPBounds.Hardy
