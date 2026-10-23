module

public import CGLMPBounds.Fourier.Basis
public import CGLMPBounds.Fourier.LocalComponent
public import CGLMPBounds.Fourier.Visibility

@[expose] public section


/-!
# Lemma F.1 for the Fourier-phase behaviour

Supplement, Lemma F.1: for every `d ≥ 2`, `Q_d ≥ a_d L_d` entrywise (F.2), the coefficient `a_d` is
maximal for this `L_d`, and `v_crit(Q_d) ≥ 1/(2 - a_d) > 3049/5000` (F.3). Here `Q_d` is the
behaviour of the Fourier-phase measurements (B.2) on `Φ_d`.

* `localWeight_mul_localComponent_le_fourierTable` : (F.2);
* `le_localWeight_of_le_fourierTable` : maximality of `a_d`;
* `one_div_two_sub_localWeight_le_critVisibility`, `lt_critVisibility_fourierTable` : (F.3);
* `localComponent_apply_residual` : the entries of `L_d` through the residual.
-/

namespace CGLMPBounds

noncomputable section

variable (d : ℕ) [NeZero d]

/-- Equation (F.2): `Q_d ≥ a_d L_d` entrywise. -/
theorem localWeight_mul_localComponent_le_fourierTable (hd : 2 ≤ d) (x y : Fin 2)
    (a b : ZMod d) :
    localWeight d * localComponent d x y a b ≤ fourierTable d x y a b := by
  rw [fourierTable_apply]
  exact localWeight_mul_localComponent_le d hd x y a b

/-- `a_d` is maximal for `L_d`: no larger multiple of `L_d` lies below `Q_d`. -/
theorem le_localWeight_of_le_fourierTable (hd : 2 ≤ d) {α : ℝ}
    (h : ∀ x y a b, α * localComponent d x y a b ≤ fourierTable d x y a b) :
    α ≤ localWeight d :=
  le_localWeight_of_le d hd (fun x y a b => (h x y a b).trans_eq (fourierTable_apply d x y a b))

/-- The normalised remainder `(Q_d - a_d L_d)/(1 - a_d)`. -/
def fourierRemainder : Table (ZMod d) (ZMod d) :=
  (1 / (1 - localWeight d)) • (fourierTable d - localWeight d • localComponent d)

/-- Entries of `L_d` through the residual: `3/(4d)` at `r = 0` and `1/(4d)` at `r = d - 1`. -/
theorem localComponent_apply_residual (x y : Fin 2) (a b : ZMod d) :
    localComponent d x y a b = 1 / (d : ℝ) * (3 / 4 * (if residual d x y a b = 0 then 1 else 0)
      + 1 / 4 * (if residual d x y a b = d - 1 then 1 else 0)) := by
  rw [localComponent_apply, residual_eq_val]
  simp only [ZMod.val_eq_zero, zmod_val_eq_sub_one_iff]
  ring

/-- Equation (F.3), first inequality: `v_crit(Q_d) ≥ 1/(2 - a_d)`. -/
theorem one_div_two_sub_localWeight_le_critVisibility (hd : 2 ≤ d) :
    1 / (2 - localWeight d) ≤ critVisibility (fourierTable d) := by
  have hα1 : localWeight d < 1 := lt_of_le_of_lt (localWeight_le d hd) (by norm_num)
  have hα0 : 0 ≤ localWeight d :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1098 / 3049) (localWeight_gt d hd).le
  have h1α : (0 : ℝ) < 1 - localWeight d := by linarith
  have hc : 1 / (1 - localWeight d) * (1 - localWeight d) = 1 := one_div_mul_cancel h1α.ne'
  have hq : fourierTable d
      = localWeight d • localComponent d + (1 - localWeight d) • fourierRemainder d := by
    funext x y a b
    simp only [fourierRemainder, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination
      (-(fourierTable d x y a b - localWeight d * localComponent d x y a b)) * hc
  have hr0 : ∀ x y a b, 0 ≤ fourierRemainder d x y a b := by
    intro x y a b
    simp only [fourierRemainder, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    exact mul_nonneg (div_nonneg zero_le_one h1α.le)
      (sub_nonneg.mpr (localWeight_mul_localComponent_le_fourierTable d hd x y a b))
  have hrA : ∀ x y a, ∑ b, fourierRemainder d x y a b
      = 1 / (Fintype.card (ZMod d) : ℝ) := by
    intro x y a
    simp only [fourierRemainder, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fourierTable_right,
      sum_localComponent_right, ZMod.card]
    linear_combination (1 / (d : ℝ)) * hc
  have hrB : ∀ x y b, ∑ a, fourierRemainder d x y a b
      = 1 / (Fintype.card (ZMod d) : ℝ) := by
    intro x y b
    simp only [fourierRemainder, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_fourierTable_left,
      sum_localComponent_left, ZMod.card]
    linear_combination (1 / (d : ℝ)) * hc
  exact le_critVisibility_of_local_part hα1.le hα0 (localComponent_mem_localSet d)
    (half_noise_mem_localSet hr0 hrA hrB) hq

/-- Equation (F.3): `v_crit(Q_d) ≥ 1/(2 - a_d) > 3049/5000`. -/
theorem lt_critVisibility_fourierTable (hd : 2 ≤ d) :
    (3049 : ℝ) / 5000 < critVisibility (fourierTable d) :=
  lt_of_lt_of_le (visibility_bound d hd) (one_div_two_sub_localWeight_le_critVisibility d hd)

/-! ### Lemma F.1 as stated in the supplement (explicit formulas) -/

/-- Equation (F.1) with the closed formula written out. -/
theorem fourierTable_apply_explicit (x y : Fin 2) (a b : ZMod d) :
    fourierTable d x y a b = 1 / (2 * (d : ℝ) ^ 2
      * Real.sin (Real.pi * ((residual d x y a b : ℝ) + 1 / 4) / (d : ℝ)) ^ 2) / d :=
  fourierTable_apply d x y a b

/-- Lemma F.1, local component: `L_d` is Bell-local, has residual law `3/4, 1/4` at `0, d - 1`
with a uniform anchor, `Q_d ≥ a_d L_d` (F.2), and `a_d` is maximal for it. -/
theorem lemmaF1_localComponent_spec (hd : 2 ≤ d) :
    ∃ L ∈ localSet (ZMod d) (ZMod d),
      (∀ x y a b, L x y a b = 1 / (d : ℝ) * (3 / 4 * (if residual d x y a b = 0 then 1 else 0)
          + 1 / 4 * (if residual d x y a b = d - 1 then 1 else 0))) ∧
      (∀ x y a b, 2 / ((d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2) * L x y a b
          ≤ fourierTable d x y a b) ∧
      ∀ α : ℝ, (∀ x y a b, α * L x y a b ≤ fourierTable d x y a b) →
        α ≤ 2 / ((d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2) :=
  ⟨localComponent d, localComponent_mem_localSet d, localComponent_apply_residual d,
    localWeight_mul_localComponent_le_fourierTable d hd,
    fun _ h => le_localWeight_of_le_fourierTable d hd h⟩

/-- Lemma F.1, weight bounds: `9/25 < 32/(9π²) ≤ a_d ≤ 8/9`. -/
theorem lemmaF1_weight_spec (hd : 2 ≤ d) :
    (9 : ℝ) / 25 < 32 / (9 * Real.pi ^ 2) ∧
      32 / (9 * Real.pi ^ 2) ≤ 2 / ((d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2) ∧
      2 / ((d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2) ≤ 8 / 9 :=
  ⟨lt_localWeight_lower, localWeight_ge d hd, localWeight_le d hd⟩

/-- Lemma F.1, equation (F.3): `v_crit(Q_d) ≥ 1/(2 - a_d) > 3049/5000`. -/
theorem lemmaF1_visibility_spec (hd : 2 ≤ d) :
    1 / (2 - 2 / ((d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2))
        ≤ critVisibility (fourierTable d) ∧
      (3049 : ℝ) / 5000
        < 1 / (2 - 2 / ((d : ℝ) ^ 2 * Real.sin (3 * Real.pi / (4 * (d : ℝ))) ^ 2)) :=
  ⟨one_div_two_sub_localWeight_le_critVisibility d hd, visibility_bound d hd⟩

end

end CGLMPBounds
