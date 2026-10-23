module

public import CGLMPBounds.Defs.StatisticalConstants
public import Mathlib

@[expose] public section


/-!
# The Fourier-phase residual law and the local weight `a_d`

Manuscript locators: Appendix F.1, equations (F.1)–(F.3) and the proof of Lemma F.1.

For an integer `d ≥ 2` the residual law of the Fourier-phase behaviour is
`f_d(r) = 1 / (2 d² sin²(π (r + 1/4) / d))` and the local weight is
`a_d = 4 f_d(d - 1) = 2 / (d² sin²(3π / (4d)))`.

Main results:
* `localWeight_eq_four_mul`         : `a_d = 4 f_d(d - 1)` (uses `sin (π - t) = sin t`);
* `three_mul_fourierResidualLaw_le` : `3 f_d(d - 1) ≤ f_d(0)`;
* `lt_localWeight_lower`            : `9/25 < 32 / (9 π²)`;
* `localWeight_ge`, `localWeight_le`: `32 / (9 π²) ≤ a_d ≤ 8/9`
  (from `2 t / π ≤ sin t ≤ t` on `[0, π/2]` with `t = 3π / (4d)`);
* `localWeight_gt`                  : `1098/3049 < a_d`;
* `visibility_bound`                : `3049/5000 < 1 / (2 - a_d)`.

The only numerical input is Mathlib's `Real.pi_lt_d4 : π < 3.1416`.
-/

namespace CGLMPBounds

noncomputable section

/-- (F.1) the residual law of the Fourier-phase behaviour: f_d(r) = 1 / (2 d² sin²(π (r + 1/4) / d)). -/
def fourierResidualLaw (d : ℕ) (r : ℕ) : ℝ :=
  1 / (2 * (d : ℝ) ^ 2 * Real.sin (Real.pi * ((r : ℝ) + 1 / 4) / (d : ℝ)) ^ 2)

/-! ### Auxiliary real arithmetic (no trigonometry) -/

/-- `π < 3.1416`, written as a ratio of integers. -/
private theorem pi_lt_aux : Real.pi < 3927 / 1250 :=
  lt_of_lt_of_le Real.pi_lt_d4 (by norm_num)

/-- `π² < 9.87`. -/
private theorem pi_sq_lt_aux : Real.pi ^ 2 < 987 / 100 := by
  have hpi : Real.pi < 3927 / 1250 := pi_lt_aux
  have hpos : 0 < Real.pi := Real.pi_pos
  have hprod : 0 < Real.pi * (3927 / 1250 - Real.pi) := mul_pos hpos (sub_pos.mpr hpi)
  nlinarith [hprod]

/-- With `s = sin x`, `0 < s ≤ 1/2` and `sin 3x = 3 s - 4 s³`: `3 / (2 D² sin² 3x) ≤ 1 / (2 D² s²)`. -/
private theorem three_mul_one_div_le_aux (D s : ℝ) (hD : 0 < D) (hs0 : 0 < s)
    (hs1 : s ≤ 1 / 2) :
    3 * (1 / (2 * D ^ 2 * (3 * s - 4 * s ^ 3) ^ 2)) ≤ 1 / (2 * D ^ 2 * s ^ 2) := by
  have hprod : 0 ≤ s * (1 / 2 - s) := mul_nonneg hs0.le (sub_nonneg.mpr hs1)
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [hprod]
  have hfac : 3 * s - 4 * s ^ 3 = s * (3 - 4 * s ^ 2) := by ring
  have hpos3 : 0 < 3 * s - 4 * s ^ 3 := by
    rw [hfac]
    exact mul_pos hs0 (by linarith)
  have h4 : 0 ≤ s ^ 4 := by positivity
  have hexp : (3 * s - 4 * s ^ 3) ^ 2 - 3 * s ^ 2 = s ^ 2 * (6 - 24 * s ^ 2 + 16 * s ^ 4) := by
    ring
  have hnn : 0 ≤ s ^ 2 * (6 - 24 * s ^ 2 + 16 * s ^ 4) :=
    mul_nonneg (sq_nonneg s) (by linarith)
  have hkey : 3 * s ^ 2 ≤ (3 * s - 4 * s ^ 3) ^ 2 := by linarith
  have hD2 : 0 < D ^ 2 := pow_pos hD 2
  have hA : 0 < 2 * D ^ 2 * s ^ 2 := mul_pos (mul_pos (by norm_num) hD2) (pow_pos hs0 2)
  have hB : 0 < 2 * D ^ 2 * (3 * s - 4 * s ^ 3) ^ 2 :=
    mul_pos (mul_pos (by norm_num) hD2) (pow_pos hpos3 2)
  have hmul : D ^ 2 * (3 * s ^ 2) ≤ D ^ 2 * (3 * s - 4 * s ^ 3) ^ 2 :=
    mul_le_mul_of_nonneg_left hkey hD2.le
  rw [mul_one_div, div_le_div_iff₀ hB hA]
  linarith

/-- From `S ≤ 3 P / (4 D)` (in the form `S * (4 D) ≤ 3 P`): `32 / (9 P²) ≤ 2 / (D² S²)`. -/
private theorem le_two_div_aux (D S P : ℝ) (hD : 0 < D) (hS : 0 < S) (hP : 0 < P)
    (h : S * (4 * D) ≤ 3 * P) : 32 / (9 * P ^ 2) ≤ 2 / (D ^ 2 * S ^ 2) := by
  have h0 : 0 ≤ S * (4 * D) := mul_nonneg hS.le (mul_nonneg (by norm_num) hD.le)
  have hsq : S * (4 * D) * (S * (4 * D)) ≤ 3 * P * (3 * P) := mul_self_le_mul_self h0 h
  have hA : 0 < 9 * P ^ 2 := mul_pos (by norm_num) (pow_pos hP 2)
  have hB : 0 < D ^ 2 * S ^ 2 := mul_pos (pow_pos hD 2) (pow_pos hS 2)
  rw [div_le_div_iff₀ hA hB]
  linarith

/-- From `3 / (2 D) ≤ S` (in the form `3 ≤ S * (2 D)`): `2 / (D² S²) ≤ 8/9`. -/
private theorem two_div_le_aux (D S : ℝ) (hD : 0 < D) (hS : 0 < S) (h : 3 ≤ S * (2 * D)) :
    2 / (D ^ 2 * S ^ 2) ≤ 8 / 9 := by
  have hsq : (3 : ℝ) * 3 ≤ S * (2 * D) * (S * (2 * D)) :=
    mul_self_le_mul_self (by norm_num) h
  have hB : 0 < D ^ 2 * S ^ 2 := mul_pos (pow_pos hD 2) (pow_pos hS 2)
  rw [div_le_div_iff₀ hB (by norm_num : (0 : ℝ) < 9)]
  linarith

/-! ### The angles `x = π / (4d)` and `3x = 3π / (4d)` -/

theorem fourierAngle_pos (d : ℕ) (hd : 2 ≤ d) : 0 < Real.pi / (4 * (d : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  exact div_pos Real.pi_pos h4d

/-- `x = π / (4d) ≤ π / 8 ≤ 1/2` for `d ≥ 2`. -/
theorem fourierAngle_le_half (d : ℕ) (hd : 2 ≤ d) : Real.pi / (4 * (d : ℝ)) ≤ 1 / 2 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  rw [div_le_iff₀ h4d]
  linarith

theorem sin_fourierAngle_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < Real.sin (Real.pi / (4 * (d : ℝ))) := by
  have h0 : 0 < Real.pi / (4 * (d : ℝ)) := fourierAngle_pos d hd
  have h1 : Real.pi / (4 * (d : ℝ)) ≤ 1 / 2 := fourierAngle_le_half d hd
  have h2 : (1 : ℝ) / 2 < Real.pi := by linarith [Real.pi_gt_three]
  exact Real.sin_pos_of_pos_of_lt_pi h0 (lt_of_le_of_lt h1 h2)

theorem sin_fourierAngle_le_half (d : ℕ) (hd : 2 ≤ d) :
    Real.sin (Real.pi / (4 * (d : ℝ))) ≤ 1 / 2 :=
  le_trans (Real.sin_le (fourierAngle_pos d hd).le) (fourierAngle_le_half d hd)

theorem three_fourierAngle_pos (d : ℕ) (hd : 2 ≤ d) : 0 < 3 * Real.pi / (4 * (d : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  have h3pi : 0 < 3 * Real.pi := by linarith [Real.pi_pos]
  exact div_pos h3pi h4d

/-- `3x = 3π / (4d) ≤ 3π / 8 ≤ π / 2` for `d ≥ 2`. -/
theorem three_fourierAngle_le (d : ℕ) (hd : 2 ≤ d) :
    3 * Real.pi / (4 * (d : ℝ)) ≤ Real.pi / 2 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hprod : 0 ≤ Real.pi * ((d : ℝ) - 2) := mul_nonneg hpi.le (sub_nonneg.mpr hd2)
  rw [div_le_iff₀ h4d]
  nlinarith [hprod]

theorem sin_three_fourierAngle_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < Real.sin (3 * Real.pi / (4 * (d : ℝ))) := by
  have h0 : 0 < 3 * Real.pi / (4 * (d : ℝ)) := three_fourierAngle_pos d hd
  have h1 : 3 * Real.pi / (4 * (d : ℝ)) ≤ Real.pi / 2 := three_fourierAngle_le d hd
  have h2 : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi h0 (lt_of_le_of_lt h1 h2)

/-! ### The two values of the residual law used in Lemma F.1 -/

/-- `f_d(0) = 1 / (2 d² sin²(π / (4d)))`. -/
theorem fourierResidualLaw_zero (d : ℕ) :
    fourierResidualLaw d 0 =
      1 / (2 * (d : ℝ) ^ 2 * Real.sin (Real.pi / (4 * (d : ℝ))) ^ 2) := by
  have harg : Real.pi * (((0 : ℕ) : ℝ) + 1 / 4) / (d : ℝ) = Real.pi / (4 * (d : ℝ)) := by
    rw [Nat.cast_zero]
    ring
  unfold fourierResidualLaw
  rw [harg]

/-- `f_d(d - 1) = 1 / (2 d² sin²(3π / (4d)))`, by `sin (π - t) = sin t`. -/
theorem fourierResidualLaw_pred (d : ℕ) (hd : 2 ≤ d) :
    fourierResidualLaw d (d - 1) =
      1 / (2 * (d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := by
    intro h0
    linarith
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := Nat.cast_pred (by omega)
  have h1 : (d : ℝ) / (d : ℝ) = 1 := div_self hdne
  have h2 : Real.pi * ((d : ℝ) - 1 + 1 / 4) / (d : ℝ) =
      Real.pi * ((d : ℝ) / (d : ℝ)) - 3 * Real.pi / (4 * (d : ℝ)) := by
    ring
  have harg : Real.pi * (((d - 1 : ℕ) : ℝ) + 1 / 4) / (d : ℝ) =
      Real.pi - 3 * Real.pi / (4 * (d : ℝ)) := by
    rw [hcast, h2, h1, mul_one]
  unfold fourierResidualLaw
  rw [harg, Real.sin_pi_sub]

/-! ### Lemma F.1 -/

/-- `a_d = 4 f_d(d - 1)`. -/
theorem localWeight_eq_four_mul (d : ℕ) (hd : 2 ≤ d) :
    localWeight d = 4 * fourierResidualLaw d (d - 1) := by
  rw [fourierResidualLaw_pred d hd]
  unfold localWeight
  ring

/-- `3 f_d(d - 1) ≤ f_d(0)`: with `x = π / (4d) ≤ π / 8`, `(sin 3x / sin x)² = (3 - 4 sin² x)² ≥ 3`. -/
theorem three_mul_fourierResidualLaw_le (d : ℕ) (hd : 2 ≤ d) :
    3 * fourierResidualLaw d (d - 1) ≤ fourierResidualLaw d 0 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hs0 : 0 < Real.sin (Real.pi / (4 * (d : ℝ))) := sin_fourierAngle_pos d hd
  have hs1 : Real.sin (Real.pi / (4 * (d : ℝ))) ≤ 1 / 2 := sin_fourierAngle_le_half d hd
  have harg : 3 * Real.pi / (4 * (d : ℝ)) = 3 * (Real.pi / (4 * (d : ℝ))) := by ring
  have h3 : Real.sin (3 * Real.pi / (4 * (d : ℝ))) =
      3 * Real.sin (Real.pi / (4 * (d : ℝ))) - 4 * Real.sin (Real.pi / (4 * (d : ℝ))) ^ 3 := by
    rw [harg, Real.sin_three_mul]
  rw [fourierResidualLaw_pred d hd, fourierResidualLaw_zero d, h3]
  exact three_mul_one_div_le_aux (d : ℝ) (Real.sin (Real.pi / (4 * (d : ℝ)))) hdpos hs0 hs1

/-- `9/25 < 32 / (9 π²)`. -/
theorem lt_localWeight_lower : (9 : ℝ) / 25 < 32 / (9 * Real.pi ^ 2) := by
  have hsq : Real.pi ^ 2 < 987 / 100 := pi_sq_lt_aux
  have hden : 0 < 9 * Real.pi ^ 2 := mul_pos (by norm_num) (pow_pos Real.pi_pos 2)
  rw [lt_div_iff₀ hden]
  linarith

/-- `32 / (9 π²) ≤ a_d`, from `sin t ≤ t` at `t = 3π / (4d)`. -/
theorem localWeight_ge (d : ℕ) (hd : 2 ≤ d) : 32 / (9 * Real.pi ^ 2) ≤ localWeight d := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  have hS : 0 < Real.sin (3 * Real.pi / (4 * (d : ℝ))) := sin_three_fourierAngle_pos d hd
  have hle : Real.sin (3 * Real.pi / (4 * (d : ℝ))) ≤ 3 * Real.pi / (4 * (d : ℝ)) :=
    Real.sin_le (three_fourierAngle_pos d hd).le
  have h : Real.sin (3 * Real.pi / (4 * (d : ℝ))) * (4 * (d : ℝ)) ≤ 3 * Real.pi :=
    (le_div_iff₀ h4d).mp hle
  unfold localWeight
  exact le_two_div_aux (d : ℝ) (Real.sin (3 * Real.pi / (4 * (d : ℝ)))) Real.pi hdpos hS
    Real.pi_pos h

/-- `a_d ≤ 8/9`, from Jordan's inequality `2 t / π ≤ sin t` at `t = 3π / (4d) ≤ π / 2`. -/
theorem localWeight_le (d : ℕ) (hd : 2 ≤ d) : localWeight d ≤ 8 / 9 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  have hS : 0 < Real.sin (3 * Real.pi / (4 * (d : ℝ))) := sin_three_fourierAngle_pos d hd
  have hjordan : 2 / Real.pi * (3 * Real.pi / (4 * (d : ℝ))) ≤
      Real.sin (3 * Real.pi / (4 * (d : ℝ))) :=
    Real.mul_le_sin (three_fourierAngle_pos d hd).le (three_fourierAngle_le d hd)
  have h1 : Real.pi / Real.pi = 1 := div_self Real.pi_ne_zero
  have h2 : 2 / Real.pi * (3 * Real.pi / (4 * (d : ℝ))) =
      Real.pi / Real.pi * (3 / (2 * (d : ℝ))) := by
    ring
  have harg : 2 / Real.pi * (3 * Real.pi / (4 * (d : ℝ))) = 3 / (2 * (d : ℝ)) := by
    rw [h2, h1, one_mul]
  have hj : 3 / (2 * (d : ℝ)) ≤ Real.sin (3 * Real.pi / (4 * (d : ℝ))) := by
    rw [← harg]
    exact hjordan
  have h : 3 ≤ Real.sin (3 * Real.pi / (4 * (d : ℝ))) * (2 * (d : ℝ)) :=
    (div_le_iff₀ h2d).mp hj
  unfold localWeight
  exact two_div_le_aux (d : ℝ) (Real.sin (3 * Real.pi / (4 * (d : ℝ)))) hdpos hS h

/-- `1098/3049 < a_d` (since `1098/3049 < 32 / (9 π²)`, i.e. `π² < 9.8733…`). -/
theorem localWeight_gt (d : ℕ) (hd : 2 ≤ d) : (1098 : ℝ) / 3049 < localWeight d := by
  have hsq : Real.pi ^ 2 < 987 / 100 := pi_sq_lt_aux
  have hden : 0 < 9 * Real.pi ^ 2 := mul_pos (by norm_num) (pow_pos Real.pi_pos 2)
  have h1 : (1098 : ℝ) / 3049 < 32 / (9 * Real.pi ^ 2) := by
    rw [lt_div_iff₀ hden]
    linarith
  exact lt_of_lt_of_le h1 (localWeight_ge d hd)

/-- `3049/5000 < 1 / (2 - a_d)`. -/
theorem visibility_bound (d : ℕ) (hd : 2 ≤ d) :
    (3049 : ℝ) / 5000 < 1 / (2 - localWeight d) := by
  have hgt : (1098 : ℝ) / 3049 < localWeight d := localWeight_gt d hd
  have hle : localWeight d ≤ 8 / 9 := localWeight_le d hd
  have hpos : 0 < 2 - localWeight d := by linarith
  rw [lt_div_iff₀ hpos]
  linarith

end

end CGLMPBounds
