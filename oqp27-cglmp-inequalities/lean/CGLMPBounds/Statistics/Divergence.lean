module

public import CGLMPBounds.Defs.Statistics

@[expose] public section


/-!
# Elementary bounds for the relative entropy

* `relEntropy_sum_nonneg` : Gibbs' inequality for the finite sum in `relEntropy`;
* `relEntropy_self` : `D(p‖p) = 0`;
* `mul_log_div_le`, `relEntropy_le_of_ge` : if `r ≥ c + s a` entrywise with `p = c + a`, `c, a ≥ 0`
  and `0 < s ≤ 1`, then `D(p‖r) ≤ (Σ_z a_z) (-log₂ s)`. This is the comparison used in the proof of
  Theorem F.2 ("`(L*)_e ≥ s_e q_e`, hence `D_μ(q‖L*) ≤ Ξ(μ)`", and its local-fraction refinement).
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal

/-- Gibbs' inequality: for nonnegative `p` with total mass one and nonnegative `r` with total mass
at most one, absolutely continuous, the finite sum defining `relEntropy p r` is nonnegative. -/
theorem relEntropy_sum_nonneg {ι : Type*} [Fintype ι] (p r : ι → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hr : ∀ z, 0 ≤ r z) (hp1 : ∑ z, p z = 1) (hr1 : ∑ z, r z ≤ 1)
    (hac : ∀ z, r z = 0 → p z = 0) :
    0 ≤ ∑ z, p z * Real.logb 2 (p z / r z) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ z, (p z - r z) / Real.log 2 ≤ p z * Real.logb 2 (p z / r z) := by
    intro z
    rcases eq_or_lt_of_le (hp z) with h | h
    · rw [← h, zero_mul, zero_sub, neg_div]
      exact neg_nonpos.mpr (div_nonneg (hr z) hlog2.le)
    · have hrz : 0 < r z := lt_of_le_of_ne (hr z) (fun h' => h.ne' (hac z h'.symm))
      have h1 := Real.one_sub_inv_le_log_of_pos (div_pos h hrz)
      rw [inv_div] at h1
      have h2 : p z - r z ≤ p z * Real.log (p z / r z) := by
        have h3 := mul_le_mul_of_nonneg_left h1 h.le
        rw [mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ h.ne'] at h3
        exact h3
      have e : p z * Real.logb 2 (p z / r z) = p z * Real.log (p z / r z) / Real.log 2 := by
        unfold Real.logb
        ring
      rw [e]
      exact div_le_div_of_nonneg_right h2 hlog2.le
  have hsum : 0 ≤ ∑ z, (p z - r z) / Real.log 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hp1]
    exact div_nonneg (by linarith) hlog2.le
  exact hsum.trans (Finset.sum_le_sum (fun z _ => key z))

/-- `D(p‖p) = 0`. -/
theorem relEntropy_self {ι : Type*} [Fintype ι] (p : ι → ℝ) : relEntropy p p = 0 := by
  unfold relEntropy
  rw [if_pos (fun z h => h)]
  have h0 : ∑ z, p z * Real.logb 2 (p z / p z) = 0 := by
    refine Finset.sum_eq_zero (fun z _ => ?_)
    by_cases h : p z = 0
    · rw [h, zero_mul]
    · rw [div_self h, Real.logb_one, mul_zero]
  rw [h0, ENNReal.ofReal_zero]

/-- Pointwise comparison: `(c + a) log((c + a)/r) ≤ a (-log s)` when `r ≥ c + s a`, `c, a ≥ 0`,
`0 < s ≤ 1` and `c + a > 0` (concavity of `log` at the points `1` and `s`). -/
theorem mul_log_div_le {c a s r : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hr : c + s * a ≤ r) (hp : 0 < c + a) :
    (c + a) * Real.log ((c + a) / r) ≤ a * -Real.log s := by
  have hcs : 0 < c + s * a := by
    have h1 : s * (c + a) ≤ c + s * a := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hs1)]
    have h2 : 0 < s * (c + a) := mul_pos hs0 hp
    linarith
  have hr0 : 0 < r := lt_of_lt_of_le hcs hr
  have h1 : Real.log ((c + a) / r) ≤ Real.log ((c + a) / (c + s * a)) :=
    Real.log_le_log (div_pos hp hr0) (div_le_div_of_nonneg_left hp.le hcs hr)
  have hw : c / (c + a) + a / (c + a) = 1 := by
    rw [← add_div, div_self hp.ne']
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr one_pos)
    (Set.mem_Ioi.mpr hs0) (div_nonneg hc hp.le) (div_nonneg ha hp.le) hw
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hconc
  have h2 : c / (c + a) + a / (c + a) * s = (c + s * a) / (c + a) := by
    rw [div_mul_eq_mul_div, ← add_div, mul_comm a s]
  rw [h2] at hconc
  have h3 : Real.log ((c + s * a) / (c + a)) = -Real.log ((c + a) / (c + s * a)) := by
    rw [← Real.log_inv, inv_div]
  rw [h3] at hconc
  have h4 : a * Real.log s ≤ -((c + a) * Real.log ((c + a) / (c + s * a))) := by
    have h5 := mul_le_mul_of_nonneg_left hconc hp.le
    have e : (c + a) * (a / (c + a) * Real.log s) = a * Real.log s := by
      rw [← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hp.ne']
    rw [e, mul_neg] at h5
    exact h5
  have h6 := mul_le_mul_of_nonneg_left h1 hp.le
  linarith

/-- If `p = c + a` and `r ≥ c + s a` entrywise, with `c, a ≥ 0` and `0 < s ≤ 1`, then
`D(p‖r) ≤ (Σ_z a_z) (-log₂ s)`. -/
theorem relEntropy_le_of_ge {ι : Type*} [Fintype ι] {p r c a : ι → ℝ} {s : ℝ}
    (hpc : ∀ z, p z = c z + a z) (hc : ∀ z, 0 ≤ c z) (ha : ∀ z, 0 ≤ a z)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hr : ∀ z, c z + s * a z ≤ r z) :
    relEntropy p r ≤ ENNReal.ofReal ((∑ z, a z) * -Real.logb 2 s) := by
  have hac : ∀ z, r z = 0 → p z = 0 := by
    intro z hz
    have h1 := hr z
    rw [hz] at h1
    have h2 := mul_nonneg hs0.le (ha z)
    have hcz : c z = 0 := le_antisymm (by linarith) (hc z)
    have haz : a z = 0 := by
      have h3 : s * a z = 0 := le_antisymm (by linarith [hc z]) h2
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hs0.ne'
      · exact h
    rw [hpc z, hcz, haz, add_zero]
  unfold relEntropy
  rw [if_pos hac]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun z _ => ?_)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1
  have e1 : p z * Real.logb 2 (p z / r z)
      = (c z + a z) * Real.log ((c z + a z) / r z) / Real.log 2 := by
    rw [hpc z]
    unfold Real.logb
    ring
  have e2 : a z * -Real.logb 2 s = a z * -Real.log s / Real.log 2 := by
    unfold Real.logb
    ring
  rw [e1, e2]
  refine div_le_div_of_nonneg_right ?_ hlog2.le
  rcases eq_or_lt_of_le (add_nonneg (hc z) (ha z)) with h | h
  · rw [← h, zero_mul]
    exact mul_nonneg (ha z) (neg_nonneg.mpr hlogs)
  · exact mul_log_div_le (hc z) (ha z) hs0 hs1 (hr z) h

end

end CGLMPBounds
