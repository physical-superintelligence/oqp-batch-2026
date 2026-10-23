module

public import CGLMPBounds.CGLMP.FourierValue

@[expose] public section


/-!
# The weighted Fourier pairing and its oriented imaginary part

The existing `fourier_pair` computes the specialization `z=1`. Here the two
coefficients multiply `conj(z)` and `z`, respectively, as required when
`z_jk=τ(V_j†V_k)`. This order produces the positive cosecant contribution in
the source one-edge cost.
-/

namespace CGLMPBounds.Companion
noncomputable section
open Finset

lemma pair_difference_identity {u v : ℂ} (huv : u * v = 1)
    (hu4 : u ^ 4 - 1 ≠ 0) (hv4 : v ^ 4 - 1 ≠ 0) (hdiff : u - v ≠ 0) :
    u / (u ^ 4 - 1) - v / (v ^ 4 - 1) = 1 / (u - v) := by
  rw [div_sub_div _ _ hu4 hv4, div_eq_div_iff (mul_ne_zero hu4 hv4) hdiff]
  linear_combination
    -(u ^ 4 + u ^ 3 * v ^ 3 - u ^ 3 * v + u ^ 2 * v ^ 2 - u ^ 2 -
      u * v ^ 3 + u * v + v ^ 4 - v ^ 2 - 1) * huv

lemma weighted_pair_identity {u v : ℂ} (huv : u * v = 1)
    (hu4 : u ^ 4 - 1 ≠ 0) (hv4 : v ^ 4 - 1 ≠ 0)
    (hsum : u + v ≠ 0) (hdiff : u - v ≠ 0) (z : ℂ) :
    v / (v ^ 4 - 1) * star z + u / (u ^ 4 - 1) * z =
      -(z.re : ℂ) / (u + v) + (z.im : ℂ) * Complex.I / (u - v) := by
  have hplus := pair_identity huv hu4 hv4 hsum
  have hminus := pair_difference_identity huv hu4 hv4 hdiff
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have hstar : star z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination
    (v / (v ^ 4 - 1)) * hstar + (u / (u ^ 4 - 1)) * hz +
    (z.re : ℂ) * hplus + ((z.im : ℂ) * Complex.I) * hminus

lemma etaD_pow_exp (d h : ℕ) :
    etaD d ^ h = Complex.exp (((Real.pi * h / (2 * d) : ℝ) : ℂ) * Complex.I) := by
  unfold etaD
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma etaD_inv_pow_exp (d h : ℕ) :
    (etaD d)⁻¹ ^ h = Complex.exp (((-(Real.pi * h / (2 * d)) : ℝ) : ℂ) * Complex.I) := by
  rw [inv_pow, etaD_pow_exp, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

lemma etaD_pow_sub_inv_pow (d h : ℕ) :
    etaD d ^ h - (etaD d)⁻¹ ^ h =
      ((2 * Real.sin (Real.pi * h / (2 * d)) : ℝ) : ℂ) * Complex.I := by
  rw [etaD_pow_exp, etaD_inv_pow_exp, Complex.exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma sin_pi_mul_div_pos {d h : ℕ} (hh : 0 < h) (hhd : h < d) :
    0 < Real.sin (Real.pi * h / (2 * d)) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (lt_trans hh hhd)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hhdR : (h : ℝ) < d := by exact_mod_cast hhd
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos hhR) (mul_pos two_pos hd)
  · rw [div_lt_iff₀ (mul_pos two_pos hd)]
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hhdR), mul_pos Real.pi_pos hd]

/-- The scalar pair at gap `h`, including the source sign of `Im z`. -/
theorem weighted_eta_pair {d h : ℕ} (hh : 0 < h) (hhd : h < d) (z : ℂ) :
    (etaD d)⁻¹ ^ h / (((etaD d)⁻¹ ^ h) ^ 4 - 1) * star z +
        etaD d ^ h / ((etaD d ^ h) ^ 4 - 1) * z =
      (((-z.re / (2 * Real.cos (Real.pi * h / (2 * d))) +
          z.im / (2 * Real.sin (Real.pi * h / (2 * d)))) : ℝ) : ℂ) := by
  have hd : d ≠ 0 := by omega
  have hη := etaD_ne_zero d
  have hprim := isPrimitiveRoot_etaD_pow_four hd
  have hz : (etaD d ^ 4) ^ h ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hh.ne' hhd
  have hu4 : (etaD d ^ h) ^ 4 = (etaD d ^ 4) ^ h := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hv4 : ((etaD d)⁻¹ ^ h) ^ 4 = ((etaD d ^ 4) ^ h)⁻¹ := by
    rw [inv_pow, inv_pow, hu4]
  have huv : etaD d ^ h * (etaD d)⁻¹ ^ h = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hη, one_pow]
  have hU : (etaD d ^ h) ^ 4 - 1 ≠ 0 := by
    rw [hu4]
    exact sub_ne_zero.mpr hz
  have hV : ((etaD d)⁻¹ ^ h) ^ 4 - 1 ≠ 0 := by
    rw [hv4]
    exact sub_ne_zero.mpr (inv_ne_one.mpr hz)
  have hc := cos_pi_mul_div_pos hhd
  have hs := sin_pi_mul_div_pos hh hhd
  have hsum : etaD d ^ h + (etaD d)⁻¹ ^ h ≠ 0 := by
    rw [etaD_pow_add_inv_pow]
    exact Complex.ofReal_ne_zero.mpr (mul_pos two_pos hc).ne'
  have hdiff : etaD d ^ h - (etaD d)⁻¹ ^ h ≠ 0 := by
    rw [etaD_pow_sub_inv_pow]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos two_pos hs).ne') Complex.I_ne_zero
  rw [weighted_pair_identity huv hU hV hsum hdiff z,
    etaD_pow_add_inv_pow, etaD_pow_sub_inv_pow]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hc.ne', Complex.ofReal_ne_zero.mpr hs.ne',
    Complex.I_ne_zero] <;> ring

/-- The full paired weighted residue sums for `j<k`, before taking real parts. -/
theorem weighted_fourier_pair {d j k : ℕ} (hjk : j < k) (hkd : k < d) (z : ℂ) :
    ((etaD d ^ j * (etaD d)⁻¹ ^ k) *
        ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ k) ^ r) * star z +
      ((etaD d ^ k * (etaD d)⁻¹ ^ j) *
        ∑ r ∈ range d, (r : ℂ) * ((etaD d ^ 4) ^ k * (etaD d ^ 4)⁻¹ ^ j) ^ r) * z =
      (((-(d : ℝ) * z.re / (2 * Real.cos (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d))) +
        (d : ℝ) * z.im / (2 * Real.sin (Real.pi * ((k - j : ℕ) : ℝ) / (2 * d)))) : ℝ) : ℂ) := by
  have hd : d ≠ 0 := by omega
  have hη := etaD_ne_zero d
  have hη4 : etaD d ^ 4 ≠ 0 := pow_ne_zero 4 hη
  have hprim := isPrimitiveRoot_etaD_pow_four hd
  obtain ⟨h, rfl⟩ : ∃ h, k = j + h := ⟨k - j, by omega⟩
  have hh : 0 < h := by omega
  have hhd : h < d := by omega
  rw [show j + h - j = h by omega]
  have eA : etaD d ^ j * (etaD d)⁻¹ ^ (j + h) = (etaD d)⁻¹ ^ h := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hη, one_pow, one_mul]
  have eB : etaD d ^ (j + h) * (etaD d)⁻¹ ^ j = etaD d ^ h := by
    rw [pow_add, mul_comm (etaD d ^ j), mul_assoc, ← mul_pow, mul_inv_cancel₀ hη,
      one_pow, mul_one]
  have eC : (etaD d ^ 4) ^ j * (etaD d ^ 4)⁻¹ ^ (j + h) = ((etaD d ^ 4) ^ h)⁻¹ := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hη4, one_pow, one_mul, inv_pow]
  have eD : (etaD d ^ 4) ^ (j + h) * (etaD d ^ 4)⁻¹ ^ j = (etaD d ^ 4) ^ h := by
    rw [pow_add, mul_comm ((etaD d ^ 4) ^ j), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hη4, one_pow, mul_one]
  rw [eA, eB, eC, eD]
  have hz : (etaD d ^ 4) ^ h ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hh.ne' hhd
  have hzd : ((etaD d ^ 4) ^ h) ^ d = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hzi : ((etaD d ^ 4) ^ h)⁻¹ ≠ 1 := inv_ne_one.mpr hz
  have hzid : (((etaD d ^ 4) ^ h)⁻¹) ^ d = 1 := by rw [inv_pow, hzd, inv_one]
  rw [sum_range_mul_pow_eq hzid hzi, sum_range_mul_pow_eq hzd hz]
  have hu4 : (etaD d ^ h) ^ 4 = (etaD d ^ 4) ^ h := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hv4 : ((etaD d)⁻¹ ^ h) ^ 4 = ((etaD d ^ 4) ^ h)⁻¹ := by
    rw [inv_pow, inv_pow, hu4]
  calc
    _ = (d : ℂ) *
        ((etaD d)⁻¹ ^ h / (((etaD d)⁻¹ ^ h) ^ 4 - 1) * star z +
          etaD d ^ h / ((etaD d ^ h) ^ 4 - 1) * z) := by
      rw [hu4, hv4]
      ring
    _ = _ := by
      rw [weighted_eta_pair hh hhd z]
      push_cast
      ring

end
end CGLMPBounds.Companion
