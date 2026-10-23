module

public import CGLMPBounds.Defs.PartitionKernel
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section


/-! The actual Abel kernel underlying D.2. Geometric summation and its
pointwise secant/cosecant limit, with the sign of the imaginary correlation
checked explicitly. The exchange of this limit with the two interval
integrals is a separate remaining obligation. -/

namespace CGLMPBounds.Partition
open Set Filter
open scoped Topology
noncomputable section

theorem quarterBranchAbelKernel_eq (q x : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    quarterBranchAbelKernel q x =
      Complex.exp (((3 * Real.pi * x / 2 : ℝ) : ℂ) * Complex.I) /
        (1 - (q : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
  let E := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  have hE : ‖(q : ℂ) * E‖ < 1 := by
    have hnorm : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq₀]
    exact hq₁
  have hterm (n : ℕ) :
      (q : ℂ) ^ n *
        Complex.exp ((((2 * Real.pi * (n : ℝ) + 3 * Real.pi / 2) * x : ℝ) : ℂ) *
          Complex.I) =
      ((q : ℂ) * E) ^ n * Complex.exp (((3 * Real.pi * x / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [mul_assoc ((q : ℂ) ^ n), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  unfold quarterBranchAbelKernel
  simp_rw [hterm]
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hE]
  simp only [div_eq_mul_inv]
  ring

private lemma quarter_denominator (a : ℝ) :
    1 - Complex.exp (((4 * a : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I) *
        (-4 * Complex.I * (Real.sin a : ℂ) * (Real.cos a : ℂ)) := by
  have he : Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (((-2 * a : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I)) =
      1 - Complex.exp (((4 * a : ℝ) : ℂ) * Complex.I) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    have hz : (((2 * a : ℝ) : ℂ) * Complex.I +
        (((-2 * a : ℝ) : ℂ) * Complex.I)) = 0 := by push_cast; ring
    have h4 : (((2 * a : ℝ) : ℂ) * Complex.I +
        (((2 * a : ℝ) : ℂ) * Complex.I)) =
        (((4 * a : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [hz, h4, Complex.exp_zero]
  rw [← he, Complex.exp_ofReal_mul_I (-2 * a), Complex.exp_ofReal_mul_I (2 * a)]
  rw [show -2 * a = -(2 * a) by ring, Real.cos_neg, Real.sin_neg, Real.sin_two_mul]
  push_cast
  ring

private lemma quarter_quotient (a : ℝ) (hs : Real.sin a ≠ 0) (hc : Real.cos a ≠ 0) :
    Complex.exp (((3 * a : ℝ) : ℂ) * Complex.I) /
      (1 - Complex.exp (((4 * a : ℝ) : ℂ) * Complex.I)) =
        -(1 / (4 * (Real.cos a : ℂ))) + Complex.I / (4 * (Real.sin a : ℂ)) := by
  have he : Complex.exp (((3 * a : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((a : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, quarter_denominator, mul_div_mul_left _ _ (Complex.exp_ne_zero _),
    Complex.exp_ofReal_mul_I]
  have hsC : (Real.sin a : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcC : (Real.cos a : ℂ) ≠ 0 := by exact_mod_cast hc
  field_simp [hsC, hcC, Complex.I_ne_zero]
  <;> ring_nf
  <;> norm_num [Complex.I_sq]

lemma quarterBranch_denominator_ne_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  have hs : Real.sin (Real.pi * x / 2) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · exact div_pos (mul_pos Real.pi_pos hx.1) (by norm_num)
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hx.2)]
  have hc : Real.cos (Real.pi * x / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    constructor <;> nlinarith [Real.pi_pos, mul_pos Real.pi_pos hx.1,
      mul_pos Real.pi_pos (sub_pos.mpr hx.2)]
  have harg : 2 * Real.pi * x = 4 * (Real.pi * x / 2) := by ring
  rw [harg, quarter_denominator]
  apply mul_ne_zero (Complex.exp_ne_zero _)
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hs)
  · exact_mod_cast hc

lemma quarterBranch_quotient_eq_secants {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Complex.exp (((3 * Real.pi * x / 2 : ℝ) : ℂ) * Complex.I) /
        (1 - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) =
      -(scalarSecant x : ℂ) / 4 + Complex.I * (scalarSecant (1 - x) : ℂ) / 4 := by
  have hs : Real.sin (Real.pi * x / 2) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi _ _).ne'
    · exact div_pos (mul_pos Real.pi_pos hx.1) (by norm_num)
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hx.2)]
  have hc : Real.cos (Real.pi * x / 2) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    constructor <;> nlinarith [Real.pi_pos, mul_pos Real.pi_pos hx.1,
      mul_pos Real.pi_pos (sub_pos.mpr hx.2)]
  have hcos : Real.cos (Real.pi * (1 - x) / 2) = Real.sin (Real.pi * x / 2) := by
    rw [show Real.pi * (1 - x) / 2 = Real.pi / 2 - Real.pi * x / 2 by ring,
      Real.cos_pi_div_two_sub]
  rw [show 3 * Real.pi * x / 2 = 3 * (Real.pi * x / 2) by ring,
    show 2 * Real.pi * x = 4 * (Real.pi * x / 2) by ring, quarter_quotient _ hs hc]
  simp only [scalarSecant, hcos, Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- The literal Abel sum tends to the source secant/cosecant kernel. -/
theorem quarterBranchAbelKernel_tendsto {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun q : ℝ => quarterBranchAbelKernel q x) (𝓝[<] (1 : ℝ))
      (𝓝 (-(scalarSecant x : ℂ) / 4 + Complex.I * (scalarSecant (1 - x) : ℂ) / 4)) := by
  have hc : ContinuousAt (fun q : ℝ =>
      Complex.exp (((3 * Real.pi * x / 2 : ℝ) : ℂ) * Complex.I) /
        (1 - (q : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))) 1 := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    simpa using quarterBranch_denominator_ne_zero hx
  have ht := hc.tendsto.mono_left
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  simp only [Complex.ofReal_one, one_mul] at ht
  rw [quarterBranch_quotient_eq_secants hx] at ht
  apply ht.congr'
  have hpos : ∀ᶠ q : ℝ in 𝓝[<] (1 : ℝ), 0 < q :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with q hq₀ hq₁
  exact (quarterBranchAbelKernel_eq q x hq₀.le hq₁).symm

/-- Pairing conjugate half-squares gives the +Im correlation in D.2. -/
theorem quarterBranch_pair_kernel_real (x : ℝ) (z : ℂ) :
    2 * ((-(scalarSecant x : ℂ) / 4 +
      Complex.I * (scalarSecant (1 - x) : ℂ) / 4) * (star z - 1)).re =
      (1 / 2 : ℝ) * (scalarSecant x * (1 - z.re) + scalarSecant (1 - x) * z.im) := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
  <;> ring

end
end CGLMPBounds.Partition
