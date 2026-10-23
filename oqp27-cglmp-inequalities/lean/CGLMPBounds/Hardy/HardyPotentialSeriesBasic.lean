module

public import CGLMPBounds.Defs.HardyPotentialSeries
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

@[expose] public section


/-! Actual uniform boundary convergence for the auxiliary odd dilogarithm,
and its derivative obtained by differentiating its true convergent series.
No identification with the C.14 double primitive is assumed here. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Metric Complex

lemma hardy_odd_reciprocal_square_summable :
    Summable (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
  exact hasSum_zeta_two.summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n + 1) by
      intro m n h
      change 2 * m + 1 = 2 * n + 1 at h
      omega)

lemma hardyOddDilog_term_norm_le (n : ℕ) {q : ℂ} (hq : ‖q‖ ≤ 1) :
    ‖(-1 : ℂ) ^ n * q ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ) ^ 2‖ ≤
      (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg q) hq) (by positivity)

lemma hardyOddDilog_summable {q : ℂ} (hq : ‖q‖ ≤ 1) :
    Summable (fun n : ℕ => (-1 : ℂ) ^ n * q ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℂ) ^ 2) :=
  hardy_odd_reciprocal_square_summable.of_norm_bounded
    (fun n => hardyOddDilog_term_norm_le n hq)

theorem continuousOn_hardyOddDilog : ContinuousOn hardyOddDilog (closedBall (0 : ℂ) 1) := by
  apply continuousOn_tsum (fun _ => by fun_prop) hardy_odd_reciprocal_square_summable
  intro n q hq
  exact hardyOddDilog_term_norm_le n (by simpa only [mem_closedBall, dist_zero_right] using hq)

theorem differentiableOn_hardyOddDilog : DifferentiableOn ℂ hardyOddDilog (ball (0 : ℂ) 1) := by
  apply differentiableOn_tsum_of_summable_norm hardy_odd_reciprocal_square_summable
    (fun _ => by fun_prop) isOpen_ball
  intro n q hq
  exact hardyOddDilog_term_norm_le n
    (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hq))

lemma hasDerivAt_hardyOddDilog_term (n : ℕ) (q : ℂ) :
    HasDerivAt (fun q : ℂ => (-1 : ℂ) ^ n * q ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℂ) ^ 2)
      ((-1 : ℂ) ^ n * q ^ (2 * n) / ((2 * n + 1 : ℕ) : ℂ)) q := by
  have hn : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
  convert (((hasDerivAt_id q).pow (2 * n + 1)).const_mul ((-1 : ℂ) ^ n)).div_const
    (((2 * n + 1 : ℕ) : ℂ) ^ 2) using 1 <;> first
    | rfl
    | (simp only [Nat.add_sub_cancel, mul_one, id_eq]; field_simp [hn] <;> ring)

theorem hasDerivAt_hardyOddDilog {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasDerivAt hardyOddDilog (Complex.arctan q / q) q := by
  have hqball : q ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hq
  have hs := hasSum_deriv_of_summable_norm hardy_odd_reciprocal_square_summable
    (F := fun n q => (-1 : ℂ) ^ n * q ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℂ) ^ 2)
    (fun _ => by fun_prop) isOpen_ball
    (fun n q hq => hardyOddDilog_term_norm_le n
      (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hq))) hqball
  simp_rw [(hasDerivAt_hardyOddDilog_term _ _).deriv] at hs
  change HasSum (fun n : ℕ => (-1 : ℂ) ^ n * q ^ (2 * n) /
    ((2 * n + 1 : ℕ) : ℂ)) (deriv hardyOddDilog q) at hs
  have hs' := hs.mul_right q
  have ht : HasSum (fun n : ℕ => (-1 : ℂ) ^ n * q ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℂ)) (deriv hardyOddDilog q * q) := by
    convert hs' using 1
    funext n
    rw [pow_succ]
    ring
  have he := ht.unique (Complex.hasSum_arctan hq)
  have hd : deriv hardyOddDilog q = Complex.arctan q / q := (eq_div_iff hq0).mpr he
  simpa only [hd] using
    (differentiableOn_hardyOddDilog.differentiableAt (isOpen_ball.mem_nhds hqball)).hasDerivAt

lemma hardyUpper_exp_norm (z : ℂ) :
    ‖Complex.exp (Complex.I * Real.pi * z / 2)‖ = Real.exp (-Real.pi * z.im / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem continuousOn_hardyUpperPotential :
    ContinuousOn hardyUpperPotential {z : ℂ | 0 ≤ z.im} := by
  apply ContinuousOn.add (by fun_prop)
  apply continuousOn_const.mul
  apply continuousOn_hardyOddDilog.comp (by fun_prop)
  intro z hz
  change 0 ≤ z.im at hz
  rw [mem_closedBall, dist_zero_right, hardyUpper_exp_norm, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos]

theorem hasDerivAt_hardyUpperPotential {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt hardyUpperPotential
      (-Complex.I + (4 * Complex.I / Real.pi) *
        Complex.arctan (Complex.exp (Complex.I * Real.pi * z / 2))) z := by
  let q := Complex.exp (Complex.I * Real.pi * z / 2)
  have hq : ‖q‖ < 1 := by
    rw [hardyUpper_exp_norm, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * Real.pi * w / 2))
      ((Complex.I * Real.pi / 2) * q) z := by
    convert (((hasDerivAt_id z).const_mul (Complex.I * Real.pi)).div_const 2).cexp using 1 <;>
      first | rfl | (dsimp [q]; ring)
  have hd := (hasDerivAt_hardyOddDilog hq hq0).comp z hexp
  convert ((hasDerivAt_id z).const_mul (-Complex.I)).add
    (hd.const_mul (8 / (Real.pi : ℂ) ^ 2)) using 1
  · rfl
  · field_simp [hq0, Real.pi_ne_zero]
    ring

theorem hardyUpperPotential_zero : hardyUpperPotential 0 = (hardyStripCenterConstant : ℂ) := by
  have hc : (∑' n : ℕ, (-1 : ℂ) ^ n / ((2 * n + 1 : ℕ) : ℂ) ^ 2) =
      (Partition.sourceCatalanConstant : ℂ) := by
    rw [Partition.sourceCatalanConstant, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    push_cast <;> ring
  simp only [hardyUpperPotential, mul_zero, zero_div, Complex.exp_zero, hardyOddDilog,
    one_pow, mul_one, zero_add]
  rw [hc, hardyStripCenterConstant, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

end
end CGLMPBounds.Hardy
