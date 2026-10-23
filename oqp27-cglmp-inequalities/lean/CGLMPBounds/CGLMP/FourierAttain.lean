module

public import CGLMPBounds.CGLMP.FourierValue

@[expose] public section


/-!
# Attainment of `I_d^F` and the witness threshold of `Q_d`

Theorem A.1 (equality for the Fourier-phase measurements on `Φ_d`) and Theorem A.3, (A.5)
("the minimum is attained"): `I_d(Q_d) = I_d^F > 2`, so the uniform-noise mixture
`v Q_d + (1 - v) u_d` violates the CGLMP inequality exactly when `v > 2/I_d^F`.

* `sum_Ico_sub` : `Σ_{h=1}^{d-1} (d - h) = d(d - 1)/2`;
* `two_lt_cglmpFourierValue` : `I_d^F > 2` for `d ≥ 2` (every secant exceeds `1`);
* `fourier_attains_cglmp_value_spec` : the form of the Challenge endpoint.
-/

namespace CGLMPBounds

noncomputable section

open Finset

theorem sum_range_natCast_real (n : ℕ) :
    ∑ k ∈ range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `Σ_{h=1}^{d-1} (d - h) = d(d - 1)/2`. -/
theorem sum_Ico_sub (d : ℕ) : ∑ h ∈ Ico 1 d, ((d : ℝ) - h) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  have h := sum_range_sum_range_sub (fun _ => (1 : ℝ)) d
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  rw [← h, sum_range_natCast_real]

/-- `I_d^F > 2` for `d ≥ 2`: each secant `sec(πh/(2d))`, `1 ≤ h < d`, exceeds `1`. -/
theorem two_lt_cglmpFourierValue (d : ℕ) (hd : 2 ≤ d) : 2 < cglmpFourierValue d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hne : (Ico 1 d).Nonempty := ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
  have hlt : ∑ h ∈ Ico 1 d, ((d : ℝ) - h)
      < ∑ h ∈ Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d)) := by
    refine Finset.sum_lt_sum_of_nonempty hne (fun h hh => ?_)
    rw [Finset.mem_Ico] at hh
    have hhd : h < d := hh.2
    have hh1 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hpos : 0 < (d : ℝ) - h := by
      have : (h : ℝ) < d := by exact_mod_cast hhd
      linarith
    have hcos0 := cos_pi_mul_div_pos hhd
    have hcos1 : Real.cos (Real.pi * h / (2 * d)) < 1 := by
      rw [← Real.cos_zero]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two le_rfl
      · rw [div_le_iff₀ (mul_pos two_pos hd0)]
        have : (h : ℝ) ≤ d := by exact_mod_cast hhd.le
        nlinarith [Real.pi_pos]
      · exact div_pos (mul_pos Real.pi_pos hh1) (mul_pos two_pos hd0)
    rw [lt_div_iff₀ hcos0]
    nlinarith
  rw [sum_Ico_sub] at hlt
  have hX : (d : ℝ) * ((d : ℝ) - 1) ≠ 0 := (mul_pos hd0 hd1).ne'
  have e : (4 : ℝ) / ((d : ℝ) * ((d : ℝ) - 1)) * ((d : ℝ) * ((d : ℝ) - 1) / 2) = 2 := by
    rw [div_mul_div_comm, mul_comm (4 : ℝ), mul_div_mul_left _ _ hX]
    norm_num
  unfold cglmpFourierValue
  calc (2 : ℝ) = 4 / ((d : ℝ) * ((d : ℝ) - 1)) * ((d : ℝ) * ((d : ℝ) - 1) / 2) := e.symm
    _ < 4 / ((d : ℝ) * ((d : ℝ) - 1))
        * ∑ h ∈ Ico 1 d, ((d : ℝ) - h) / Real.cos (Real.pi * h / (2 * d)) :=
        mul_lt_mul_of_pos_left hlt (div_pos (by norm_num) (mul_pos hd0 hd1))

/-- Theorem A.1 equality for `Q_d` and the attained witness threshold of (A.5), in the form of the
Challenge endpoint. -/
theorem fourier_attains_cglmp_value_spec (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    cglmp d (fourierTable d) = cglmpFourierValue d ∧ 2 < cglmpFourierValue d ∧
      ∀ v : ℝ, 2 < cglmp d (noisy v (fourierTable d)) ↔ 2 / cglmpFourierValue d < v := by
  have h1 := cglmp_fourierTable d hd
  have h2 := two_lt_cglmpFourierValue d hd
  have h3 : 2 < cglmp d (fourierTable d) := by rw [h1]; exact h2
  refine ⟨h1, h2, fun v => ?_⟩
  rw [← h1]
  exact two_lt_cglmp_noisy_iff d hd h3 v

end

end CGLMPBounds
