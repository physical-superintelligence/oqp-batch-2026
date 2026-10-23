module

public import CGLMPBounds.Hardy.HardyPotentialSeriesBasic

@[expose] public section


/-! Actual second derivative of the upper half-plane series. Complex
arctangent is differentiated from its convergent series on the disk. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Set Metric Complex Filter
open scoped Topology

lemma hasDerivAt_complex_arctan_disk {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt Complex.arctan (1 / (1 + q ^ 2)) q := by
  let R : ℝ := (‖q‖ + 1) / 2
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hqR : ‖q‖ < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  let F : ℕ → ℂ → ℂ := fun n z =>
    (-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ)
  have hbound : ∀ n z, z ∈ ball (0 : ℂ) R → ‖F n z‖ ≤ R ^ n := by
    intro n z hz
    have hzR : ‖z‖ ≤ R := (by simpa only [mem_ball, dist_zero_right] using hz : ‖z‖ < R).le
    calc
      ‖F n z‖ = ‖z‖ ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
        simp only [F, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
          one_pow, one_mul, Complex.norm_natCast]
      _ ≤ ‖z‖ ^ (2 * n + 1) := div_le_self (by positivity) (by norm_cast; omega)
      _ ≤ R ^ (2 * n + 1) := pow_le_pow_left₀ (norm_nonneg _) hzR _
      _ ≤ R ^ n := by
        rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
        exact mul_le_of_le_one_right (pow_nonneg hR0.le _) (pow_le_one₀ hR0.le hR1.le)
  have hsum := summable_geometric_of_lt_one hR0.le hR1
  have hdiff := differentiableOn_tsum_of_summable_norm hsum
    (F := F) (fun _ => by fun_prop) isOpen_ball hbound
  have hderterm (n : ℕ) : deriv (F n) q = (-1 : ℂ) ^ n * q ^ (2 * n) := by
    have hn : ((2 * n + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
    have hd := (((hasDerivAt_id q).pow (2 * n + 1)).const_mul ((-1 : ℂ) ^ n)).div_const
      (((2 * n + 1 : ℕ) : ℂ))
    convert hd.deriv using 1 <;> first
      | rfl
      | ((try simp only [Nat.add_sub_cancel, mul_one, id_eq]); field_simp [hn] <;> ring)
  have hqball : q ∈ ball (0 : ℂ) R := by simpa only [mem_ball, dist_zero_right] using hqR
  have hd := hasSum_deriv_of_summable_norm hsum
    (F := F) (fun _ => by fun_prop) isOpen_ball hbound hqball
  simp_rw [hderterm] at hd
  have hgeom : HasSum (fun n : ℕ => (-1 : ℂ) ^ n * q ^ (2 * n))
      (1 / (1 + q ^ 2)) := by
    have hnorm : ‖-q ^ 2‖ < 1 := by
      rw [norm_neg, norm_pow]
      nlinarith [norm_nonneg q]
    have hpow (n : ℕ) : (-q ^ 2) ^ n = (-1 : ℂ) ^ n * q ^ (2 * n) := by
      rw [show -q ^ 2 = (-1 : ℂ) * (q ^ 2) by ring, mul_pow, ← pow_mul]
    simpa only [hpow, sub_neg_eq_add, one_div] using
      hasSum_geometric_of_norm_lt_one hnorm
  have hv : deriv (fun z => ∑' n, F n z) q = 1 / (1 + q ^ 2) := hd.unique hgeom
  have he : (fun z => ∑' n, F n z) =ᶠ[𝓝 q] Complex.arctan := by
    filter_upwards [isOpen_ball.mem_nhds hqball] with z hz
    exact (Complex.hasSum_arctan
      ((by simpa only [mem_ball, dist_zero_right] using hz : ‖z‖ < R).trans hR1)).tsum_eq
  have hfinal := (hdiff.differentiableAt (isOpen_ball.mem_nhds hqball)).hasDerivAt
  rw [hv] at hfinal
  exact hfinal.congr_of_eventuallyEq he.symm

lemma hardyUpper_secant_exp (z : ℂ) :
    hardyStripSecant z =
      2 * Complex.exp (Complex.I * Real.pi * z / 2) /
        (1 + Complex.exp (Complex.I * Real.pi * z / 2) ^ 2) := by
  let q := Complex.exp (Complex.I * Real.pi * z / 2)
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have hc : Complex.cos (Real.pi * z / 2) = (q + q⁻¹) / 2 := by
    rw [Complex.cos]
    have h₁ : (Real.pi * z / 2) * Complex.I = Complex.I * Real.pi * z / 2 := by ring
    have h₂ : -(Real.pi * z / 2) * Complex.I = -(Complex.I * Real.pi * z / 2) := by ring
    rw [h₁, h₂, Complex.exp_neg]
  rw [hardyStripSecant, hc]
  by_cases hden : 1 + q ^ 2 = 0
  · have hs : q + q⁻¹ = 0 := by
      apply (mul_left_cancel₀ hq)
      field_simp
      linear_combination hden
    simp [hs, hden, q]
  · have hs : q + q⁻¹ ≠ 0 := by
      intro hs
      apply hden
      have hh := congrArg (fun a : ℂ => a * q) hs
      field_simp at hh
      linear_combination hh
    field_simp [hq, hden, hs]
    ring

theorem hardyUpperPotential_second_derivative {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv 2 hardyUpperPotential z = -hardyStripSecant z := by
  let q := Complex.exp (Complex.I * Real.pi * z / 2)
  have hq : ‖q‖ < 1 := by
    rw [hardyUpper_exp_norm, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have he : deriv hardyUpperPotential =ᶠ[𝓝 z]
      (fun w => -Complex.I + (4 * Complex.I / Real.pi) *
        Complex.arctan (Complex.exp (Complex.I * Real.pi * w / 2))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
    exact (hasDerivAt_hardyUpperPotential hw).deriv
  have hE : HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * Real.pi * w / 2))
      ((Complex.I * Real.pi / 2) * q) z := by
    convert (((hasDerivAt_id z).const_mul (Complex.I * Real.pi)).div_const 2).cexp using 1 <;>
      simp only [id_eq] <;> dsimp [q] <;> ring
  have hd := (hasDerivAt_const z (-Complex.I)).add
    (((hasDerivAt_complex_arctan_disk hq).comp z hE).const_mul (4 * Complex.I / Real.pi))
  change HasDerivAt (fun w : ℂ => -Complex.I + (4 * Complex.I / Real.pi) *
    Complex.arctan (Complex.exp (Complex.I * Real.pi * w / 2)))
    (0 + (4 * Complex.I / Real.pi) * (1 / (1 + q ^ 2) *
      ((Complex.I * Real.pi / 2) * q))) z at hd
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, he.deriv_eq, hd.deriv,
    hardyUpper_secant_exp]
  dsimp [q]
  simp only [zero_add]
  field_simp [Real.pi_ne_zero]
  simp only [Complex.I_sq]
  ring

end
end CGLMPBounds.Hardy
