module

public import CGLMPBounds.Hardy.SegmentPrimitiveAnalytic
public import CGLMPBounds.Hardy.HardyPotentialSymmetry

@[expose] public section


/-! Actual C.14 boundary values away from the two real singular points.
The series is uniformly summable and purely imaginary at the boundary
exponential argument; the actual double integral is analytic there and
has already been identified with that series. -/

namespace CGLMPBounds.Hardy
noncomputable section
open Complex

lemma hardyOddDilog_imaginary_term (n : ℕ) (t : ℝ) :
    (-1 : ℂ) ^ n * (Complex.I * t) ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℂ) ^ 2 =
      Complex.I * ((t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  calc
    _ = Complex.I * (((-1 : ℂ) ^ n) ^ 2 * (t : ℂ) ^ (2 * n + 1) /
        ((2 * n + 1 : ℕ) : ℂ) ^ 2) := by
      rw [mul_pow, pow_add, pow_mul, Complex.I_sq, pow_one]
      ring
    _ = _ := by rw [hs]; push_cast; ring

lemma hardyOddDilog_pure_imaginary {t : ℝ} (ht : |t| ≤ 1) :
    (hardyOddDilog (Complex.I * t)).re = 0 := by
  have hnorm : ‖Complex.I * (t : ℂ)‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using ht
  rw [hardyOddDilog, Complex.re_tsum (hardyOddDilog_summable hnorm)]
  simp only [hardyOddDilog_imaginary_term, Complex.I_mul_re, Complex.ofReal_im, neg_zero,
    tsum_zero]

lemma hardyUpperPotential_right_boundary {y : ℝ} (hy : 0 ≤ y) :
    (hardyUpperPotential (1 + Complex.I * y)).re = y := by
  let t : ℝ := Real.exp (-Real.pi * y / 2)
  have ht : |t| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [Real.pi_pos]
  have hexp : Complex.exp (Complex.I * Real.pi * (1 + Complex.I * y) / 2) =
      Complex.I * (t : ℂ) := by
    have ha : Complex.I * Real.pi * (1 + Complex.I * y) / 2 =
        (Real.pi : ℂ) / 2 * Complex.I + ((-Real.pi * y / 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (Real.pi : ℂ) * (y : ℂ) / 2 * Complex.I_sq
    rw [ha, Complex.exp_add, Complex.exp_pi_div_two_mul_I, ← Complex.ofReal_exp]
  have hD := hardyOddDilog_pure_imaginary ht
  rw [hardyUpperPotential, hexp, Complex.add_re]
  have hcoef : (8 / (Real.pi : ℂ) ^ 2 * hardyOddDilog (Complex.I * t)).re = 0 := by
    have hc : (8 / (Real.pi : ℂ) ^ 2) = ((8 / Real.pi ^ 2 : ℝ) : ℂ) := by
      push_cast <;> rfl
    rw [hc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hD,
      mul_zero, zero_mul, sub_self]
  rw [hcoef, add_zero]
  simp [Complex.mul_re, Complex.mul_im]

theorem hardyStripRealPotential_boundary_nonzero (y : ℝ) (hy : y ≠ 0) :
    hardyStripRealPotential 1 y = |y| ∧ hardyStripRealPotential (-1) y = |y| := by
  have hpos (v : ℝ) (hv : 0 < v) : hardyStripRealPotential 1 v = v := by
    change (hardyStripPotential (1 + Complex.I * v)).re = v
    rw [hardyStripPotential_eq_upper_of_im_pos (z := (1 : ℂ) + Complex.I * v) (by simpa using hv)]
    exact hardyUpperPotential_right_boundary hv.le
  have hright : hardyStripRealPotential 1 y = |y| := by
    rcases lt_or_gt_of_ne hy with hneg | hposy
    · rw [← hardyStripRealPotential_even_y 1 y, hpos (-y) (neg_pos.mpr hneg), abs_of_neg hneg]
    · rw [hpos y hposy, abs_of_pos hposy]
  refine ⟨hright, ?_⟩
  rw [hardyStripRealPotential_even_x, hright]

end
end CGLMPBounds.Hardy
