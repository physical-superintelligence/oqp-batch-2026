module

public import CGLMPBounds.Defs.ScalarCirculation
public import CGLMPBounds.Certificates.ScalarIntegralError
public import CGLMPBounds.Certificates.ScalarMaster

@[expose] public section


/-!
# The scalar triangle estimate used in the proof of D.1

Specialize the continuous-domain certificate to the literal integral coefficients.
-/

namespace CGLMPBounds.Certificates
noncomputable section

theorem scalarInfinite_fraction_eq_integralError (d h : ℕ) (hh0 : 0 < h) (hhd : h < d) :
    scalarInfinite (1 / d) ((h : ℝ) / d) =
      ((d : ℝ) + 1) * scalarIntegralError d (d - h) := by
  have hrepr := scalarInfinite_reciprocal_eq_integralError d (d - h) (by omega) (by omega)
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hy : 1 - ((d - h : ℕ) : ℝ) / d = (h : ℝ) / d := by
    rw [Nat.cast_sub hhd.le]
    field_simp [hd]
    <;> ring
  simpa only [hy] using hrepr

theorem scalarErrorSkew_reflect (d h : ℕ) (hh : h ≤ d) :
    scalarErrorSkew d (d - h) = -scalarErrorSkew d h := by
  unfold scalarErrorSkew
  rw [Nat.sub_sub_self hh]
  ring

/-- The exact sign and scale connecting Omega to a cyclic triangle's skew sum. -/
theorem scalarInfiniteTriangle_fraction (d : ℕ) (s : Fin 3 → ℕ)
    (hs0 : ∀ j, 0 < s j) (hsd : ∀ j, s j < d) :
    scalarInfiniteTriangle (1 / d) (fun j => (s j : ℝ) / d) =
      -(((d : ℝ) + 1) * ((d : ℝ) - 2) / d) * ∑ j, scalarErrorSkew d (s j) := by
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by have := hsd 0; omega)
  unfold scalarInfiniteTriangle
  have he (j : Fin 3) :
      scalarInfinite (1 / d) (1 - (s j : ℝ) / d) -
        scalarInfinite (1 / d) ((s j : ℝ) / d) =
          -((d : ℝ) + 1) * scalarErrorSkew d (s j) := by
    rw [scalarInfinite_reciprocal_eq_integralError d (s j) (hs0 j) (hsd j),
      scalarInfinite_fraction_eq_integralError d (s j) (hs0 j) (hsd j)]
    unfold scalarErrorSkew
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  field_simp [hd]
  <;> ring

/-- Scalar part of D.1, for arbitrary positive cyclic triangle lengths summing
to d and an independently chosen separation h. -/
theorem scalar_cyclic_triangle_margin (d h : ℕ) (hd : 3 ≤ d)
    (hh0 : 0 < h) (hhd : h < d) (s : Fin 3 → ℕ)
    (hs0 : ∀ j, 0 < s j) (hsum : ∑ j, s j = d) :
    (1 / (6 * ((d : ℝ) + 1))) ≤
      1 / (3 * ((d : ℝ) + 1)) + scalarIntegralError d h -
        (5 * ((d : ℝ) - 2) / (2 * d)) * |∑ j, scalarErrorSkew d (s j)| := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hθ : 1 / (d : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 3) := by
    refine ⟨by positivity, ?_⟩
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd)
  have hy : 1 - (h : ℝ) / d ∈ Set.Icc (1 / (d : ℝ)) (1 - 1 / d) := by
    constructor
    · apply (div_le_iff₀ hdpos).2
      have hhcast : (h : ℝ) + 1 ≤ d := by exact_mod_cast hhd
      field_simp [hdpos.ne']
      nlinarith
    · have hhle : (1 : ℝ) / d ≤ (h : ℝ) / d :=
        div_le_div_of_nonneg_right (by exact_mod_cast hh0) hdpos.le
      linarith
  have hx : ∀ j, 1 / (d : ℝ) ≤ (s j : ℝ) / d := by
    intro j
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs0 j) hdpos.le
  have hsreal : (∑ j : Fin 3, (s j : ℝ)) = (d : ℝ) := by exact_mod_cast hsum
  have hxsum : (∑ j : Fin 3, (s j : ℝ) / d) = 1 := by
    rw [← Finset.sum_div, hsreal, div_self hdpos.ne']
  have hsd : ∀ j, s j < d := by
    intro j
    have hp0 := hs0 0
    have hp1 := hs0 1
    have hp2 := hs0 2
    simp only [Fin.sum_univ_three] at hsum
    fin_cases j
    · change s 0 < d
      omega
    · change s 1 < d
      omega
    · change s 2 < d
      omega
  have hm := scalar_master_inequality (1 / d) (1 - (h : ℝ) / d)
    (fun j => (s j : ℝ) / d) hθ hy hx hxsum
  rw [scalarInfinite_reciprocal_eq_integralError d h hh0 hhd,
    scalarInfiniteTriangle_fraction d s hs0 hsd, abs_mul, abs_neg,
    abs_of_nonneg (show 0 ≤ ((d : ℝ) + 1) * ((d : ℝ) - 2) / d by
      have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have hd2 : 0 ≤ (d : ℝ) - 2 := by linarith
      positivity)] at hm
  have hscaled : (1 / 6 : ℝ) ≤ ((d : ℝ) + 1) *
      (1 / (3 * ((d : ℝ) + 1)) + scalarIntegralError d h -
        (5 * ((d : ℝ) - 2) / (2 * d)) * |∑ j, scalarErrorSkew d (s j)|) := by
    convert hm using 1
    field_simp [hdpos.ne', hd1.ne']
    <;> ring
  rw [mul_comm ((d : ℝ) + 1)] at hscaled
  have hout := (div_le_iff₀ hd1).2 hscaled
  simpa only [div_div] using hout

/-- The triangle-free d=2 scalar estimate uses the collapsed rectangle endpoint. -/
theorem scalar_two_outcome_margin :
    (1 / (6 * ((2 : ℝ) + 1))) ≤
      1 / (3 * ((2 : ℝ) + 1)) + scalarIntegralError 2 1 := by
  have hrect := scalar_rectangle_lower_bound (1 / 2) (1 / 2) (by norm_num) (by norm_num)
  have hnorm := scalarInfinite_reciprocal_eq_integralError 2 1 (by omega) (by omega)
  norm_num at hnorm hrect ⊢
  rw [hnorm] at hrect
  linarith

end
end CGLMPBounds.Certificates
