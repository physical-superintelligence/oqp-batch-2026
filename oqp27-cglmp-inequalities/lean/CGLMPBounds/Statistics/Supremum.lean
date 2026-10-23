module

public import CGLMPBounds.Statistics.Separation16
public import CGLMPBounds.TensorCHSH.PVM

@[expose] public section


/-!
# The supremum of the statistical strength over the tensor CHSH family (Theorem A.4, PVM part)

Supplement, proof of Theorem A.4: "Use `T_m` from (F.5) and the strict events `A_xy = {K_xy < m/4}`
[...] Data processing [...] gives `S_μ(T_m) ≥ min Σ_e μ_e D_bin(t_m‖z_e) ≥ t_m Ξ(μ) - h₂(t_m)`.
[...] This tends to zero. Theorem F.2 supplies the universal upper bound."

Here the events are `K_xy ≤ ⌊(m-1)/4⌋` (so `4k < m`), the convergence `t_m → 1` comes from
Chebyshev's inequality with the Bernstein-polynomial variance identity (instead of the Chernoff
rate of (F.14)), and the conclusion is `sup_m S_μ(T_m) = Ξ(μ)` for every input law `μ`.

* `binomial_variance`, `binomial_upper_tail_le`, `lowTail_ge` : Chebyshev's bound for `Bin(m, r)`;
* `negLogTwo_anti`, `xiMin_le_of_sum_le_three` : `Ξ` may be computed over `Σ_e s_e ≤ 3`;
* `mul_negLogTwo_le` : `t (-log₂ z) ≤ D_bin(t‖z) + h₂(t)`;
* `TensorCHSH.mul_xiMin_le_statStrength_add` : `t Ξ(μ) ≤ S_μ(q) + h₂(t)`;
* `iSup_statStrength_tensorCHSHTable` : `sup_m S_μ(T_m) = Ξ(μ)`.
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal Topology
open Finset Filter

/-! ### Chebyshev's bound for the binomial tail -/

theorem binomial_variance (m : ℕ) (r : ℝ) :
    ∑ j ∈ range (m + 1), ((m : ℝ) * r - j) ^ 2 * ((m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j))
      = m * r * (1 - r) := by
  have h := congrArg (Polynomial.eval r) (bernsteinPolynomial.variance (R := ℝ) m)
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, bernsteinPolynomial, nsmul_eq_mul, smul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem binomial_upper_tail_le {m k : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hk : (m : ℝ) * r < k + 1) :
    ∑ j ∈ range (m + 1), (if k < j then (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j) else 0)
      ≤ m * r * (1 - r) / ((k + 1) - m * r) ^ 2 := by
  have hpos : 0 < ((k : ℝ) + 1) - m * r := by linarith
  rw [le_div_iff₀ (pow_pos hpos 2), ← binomial_variance m r, Finset.sum_mul]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hw : 0 ≤ (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg (sub_nonneg.mpr hr1) _) (pow_nonneg hr0 _))
  split_ifs with h
  · have hj : (k : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    have hsq : (((k : ℝ) + 1) - m * r) ^ 2 ≤ ((m : ℝ) * r - j) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hj) (show (0 : ℝ) ≤ j + (k + 1) - 2 * (m * r) by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hw]
  · rw [zero_mul]
    exact mul_nonneg (sq_nonneg _) hw

theorem lowTail_ge {m k : ℕ} (hkm : k ≤ m) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hk : (m : ℝ) * r < k + 1) :
    1 - m * r * (1 - r) / ((k + 1) - m * r) ^ 2
      ≤ ∑ j ∈ range (k + 1), (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j) := by
  have htot : ∑ j ∈ range (m + 1), (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j) = 1 := by
    calc ∑ j ∈ range (m + 1), (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j)
        = ∑ j ∈ range (m + 1), r ^ j * (1 - r) ^ (m - j) * (m.choose j : ℝ) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = (r + (1 - r)) ^ m := (add_pow r (1 - r) m).symm
      _ = 1 := by ring
  have hsplit : ∑ j ∈ range (m + 1), (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j)
      = ∑ j ∈ range (m + 1), (if j ≤ k then (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j) else 0)
        + ∑ j ∈ range (m + 1),
          (if k < j then (m.choose j : ℝ) * ((1 - r) ^ (m - j) * r ^ j) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : j ≤ k
    · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · rw [if_neg h, if_pos (not_le.mp h), zero_add]
  rw [Certificates.lowSum_filter m k hkm] at hsplit
  have htail := binomial_upper_tail_le hr0 hr1 hk
  linarith

/-! ### `Ξ` over `Σ_e s_e ≤ 3` and the event lower bound -/

theorem negLogTwo_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : negLogTwo b ≤ negLogTwo a := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, negLogTwo_zero]
    exact le_top
  have hb : 0 < b := h.trans_le hab
  rw [negLogTwo_of_ne_zero hb.ne', negLogTwo_of_ne_zero h.ne']
  exact ENNReal.ofReal_le_ofReal (neg_le_neg (Real.logb_le_logb_of_le (by norm_num) h hab))

/-- `Ξ(μ)` is also the infimum over `0 ≤ s_e ≤ 1` with `Σ_e s_e ≤ 3` ("the minimum is unchanged by
replacing `Σ_e s_e = 3` with `Σ_e s_e ≤ 3`"). -/
theorem xiMin_le_of_sum_le_three {μ z : Fin 2 → Fin 2 → ℝ} (hz : ∀ x y, 0 ≤ z x y ∧ z x y ≤ 1)
    (h3 : ∑ x, ∑ y, z x y ≤ 3) :
    xiMin μ ≤ ∑ x, ∑ y, ENNReal.ofReal (μ x y) * negLogTwo (z x y) := by
  have hS4 : ∑ x, ∑ y, z x y < 4 := by linarith
  have hl0 : 0 ≤ (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y) :=
    div_nonneg (by linarith) (by linarith)
  have hl1 : (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hs : ∀ x y, 0 ≤ z x y + (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y) * (1 - z x y) ∧
      z x y + (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y) * (1 - z x y) ≤ 1 := fun x y =>
    ⟨by nlinarith [mul_nonneg hl0 (sub_nonneg.mpr (hz x y).2), (hz x y).1],
      by nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr (hz x y).2)]⟩
  have hsum : ∑ x, ∑ y, (z x y + (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y) * (1 - z x y))
      = 3 := by
    have e : ∑ x, ∑ y, (z x y + (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y) * (1 - z x y))
        = ∑ x, ∑ y, z x y + (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y)
          * (4 - ∑ x, ∑ y, z x y) := by
      simp only [Fin.sum_univ_two]
      ring
    rw [e, div_mul_cancel₀ _ (by linarith : (4 : ℝ) - ∑ x, ∑ y, z x y ≠ 0)]
    ring
  refine (xiMin_le (s := fun x y =>
    z x y + (3 - ∑ x, ∑ y, z x y) / (4 - ∑ x, ∑ y, z x y) * (1 - z x y)) hs hsum).trans ?_
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  exact mul_le_mul_of_nonneg_left (negLogTwo_anti (hz x y).1
    (by nlinarith [mul_nonneg hl0 (sub_nonneg.mpr (hz x y).2)])) zero_le

/-- `t (-log₂ z) ≤ D_bin(t‖z) + h₂(t)`, with `h₂(t) = binEntropy t / ln 2` in bits. -/
theorem mul_negLogTwo_le {t z : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ENNReal.ofReal t * negLogTwo z
      ≤ binRelEntropy t z + ENNReal.ofReal (Real.binEntropy t / Real.log 2) := by
  rcases eq_or_lt_of_le hz0 with h | h
  · rw [← h, binRelEntropy_zero ht0, top_add]
    exact le_top
  rcases eq_or_lt_of_le hz1 with h' | h'
  · rw [h', negLogTwo_of_ne_zero one_ne_zero, Real.logb_one, neg_zero, ENNReal.ofReal_zero,
      mul_zero]
    exact zero_le
  rw [binRelEntropy_of_mem h h', negLogTwo_of_ne_zero h.ne', ← ENNReal.ofReal_mul ht0.le]
  refine le_trans ?_ ENNReal.ofReal_add_le
  apply ENNReal.ofReal_le_ofReal
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log (1 - z) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hA : t * -Real.logb 2 z = (t * -Real.log z) / Real.log 2 := by
    unfold Real.logb
    ring
  have hB : t * Real.logb 2 (t / z) + (1 - t) * Real.logb 2 ((1 - t) / (1 - z))
      = (t * (Real.log t - Real.log z) + (1 - t) * (Real.log (1 - t) - Real.log (1 - z)))
        / Real.log 2 := by
    unfold Real.logb
    rw [Real.log_div ht0.ne' h.ne', Real.log_div (sub_pos.mpr ht1).ne' (sub_pos.mpr h').ne']
    ring
  have hC : Real.binEntropy t / Real.log 2
      = (t * -Real.log t + (1 - t) * -Real.log (1 - t)) / Real.log 2 := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog]
    ring
  rw [hA, hB, hC, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hlog2.le
  nlinarith [mul_nonneg (sub_pos.mpr ht1).le (neg_nonneg.mpr hl)]

namespace TensorCHSH

theorem eventProb_mem {m k : ℕ} {ℓ : Table (Fin m → Bool) (Fin m → Bool)} (hℓ : IsBehaviour ℓ)
    (x y : Fin 2) : 0 ≤ eventProb k ℓ x y ∧ eventProb k ℓ x y ≤ 1 := by
  have h0 : ∀ a b, 0 ≤ eventTable m k x y a b * ℓ x y a b := fun a b =>
    mul_nonneg (by unfold eventTable; split_ifs <;> norm_num) (hℓ.nonneg x y a b)
  have h1 : ∀ a b, eventTable m k x y a b * ℓ x y a b ≤ ℓ x y a b := fun a b => by
    unfold eventTable
    split_ifs
    · exact (one_mul _).le
    · rw [zero_mul]
      exact hℓ.nonneg x y a b
  refine ⟨Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => h0 a b)), ?_⟩
  calc eventProb k ℓ x y ≤ ∑ a, ∑ b, ℓ x y a b :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h1 a b))
    _ = 1 := hℓ.sum_eq_one x y

/-- Event lower bound for every input law: if every context of the behaviour `q` gives the event
`K_xy ≤ k` (`4k < m`) the same probability `t ∈ (0, 1)`, then `t Ξ(μ) ≤ S_μ(q) + h₂(t)`. -/
theorem mul_xiMin_le_statStrength_add {m k : ℕ} (hk : 4 * k < m)
    {q : Table (Fin m → Bool) (Fin m → Bool)} (hq : IsBehaviour q) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hqt : ∀ x y, eventProb k q x y = t) {μ : Fin 2 → Fin 2 → ℝ}
    (hμ : ∀ x y, 0 ≤ μ x y) (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    ENNReal.ofReal t * xiMin μ
      ≤ statStrength μ q + ENNReal.ofReal (Real.binEntropy t / Real.log 2) := by
  have hsumμ : ∑ x, ∑ y, ENNReal.ofReal (μ x y) = 1 := by
    rw [← ENNReal.ofReal_one, ← hμ1,
      ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hμ x y))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => hμ x y)]
  unfold statStrength
  rw [ENNReal.iInf_add]
  refine le_iInf (fun ℓ => ?_)
  rw [ENNReal.iInf_add]
  refine le_iInf (fun hℓ => ?_)
  have hℓb := (isNoSignalling_of_mem_localSet hℓ).isBehaviour
  have hz := eventProb_mem (k := k) hℓb
  have h3 := sum_eventProb_le_three hk hℓ
  calc ENNReal.ofReal t * xiMin μ
      ≤ ENNReal.ofReal t * ∑ x, ∑ y, ENNReal.ofReal (μ x y) * negLogTwo (eventProb k ℓ x y) :=
        mul_le_mul_of_nonneg_left (xiMin_le_of_sum_le_three hz h3) zero_le
    _ = ∑ x, ∑ y, ENNReal.ofReal (μ x y) * (ENNReal.ofReal t * negLogTwo (eventProb k ℓ x y)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring
    _ ≤ ∑ x, ∑ y, ENNReal.ofReal (μ x y) * (binRelEntropy t (eventProb k ℓ x y)
          + ENNReal.ofReal (Real.binEntropy t / Real.log 2)) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
          (mul_negLogTwo_le ht0 ht1 (hz x y).1 (hz x y).2) zero_le))
    _ = ∑ x, ∑ y, ENNReal.ofReal (μ x y) * binRelEntropy t (eventProb k ℓ x y)
          + ENNReal.ofReal (Real.binEntropy t / Real.log 2) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsumμ, one_mul]
    _ ≤ ∑ x, ∑ y, ENNReal.ofReal (μ x y)
          * relEntropy (fun z : (Fin m → Bool) × (Fin m → Bool) => q x y z.1 z.2)
            (fun z => ℓ x y z.1 z.2)
          + ENNReal.ofReal (Real.binEntropy t / Real.log 2) := by
        refine add_le_add (Finset.sum_le_sum (fun x _ => Finset.sum_le_sum
          (fun y _ => mul_le_mul_of_nonneg_left ?_ zero_le))) le_rfl
        rw [← hqt x y]
        exact binRelEntropy_eventProb_le k hq hℓb x y

end TensorCHSH

/-! ### The supremum -/

/-- The event threshold `k_m = ⌊(m - 1)/4⌋`, so that `4 k_m < m`. -/
def eventThreshold (m : ℕ) : ℕ := (m - 1) / 4

/-- `t_m = Pr{Bin(m, r) ≤ k_m}`. -/
def tensorTail (m : ℕ) : ℝ :=
  ∑ j ∈ range (eventThreshold m + 1), (m.choose j : ℝ)
    * ((1 - TensorCHSH.chshErrRate) ^ (m - j) * TensorCHSH.chshErrRate ^ j)

theorem chshErrRate_lt_quarter : TensorCHSH.chshErrRate < 1 / 4 := by
  unfold TensorCHSH.chshErrRate
  have h : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem tensorTail_ge {m : ℕ} (hm : 1 ≤ m) :
    1 - TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate)
        / (m * (1 / 4 - TensorCHSH.chshErrRate) ^ 2) ≤ tensorTail m := by
  have hr0 := chshErrRate_pos
  have hr1 := chshErrRate_lt_one
  have hrq := chshErrRate_lt_quarter
  have hkm : eventThreshold m ≤ m := by unfold eventThreshold; omega
  have hk4 : (m : ℝ) / 4 ≤ (eventThreshold m : ℝ) + 1 := by
    have : m ≤ 4 * eventThreshold m + 4 := by unfold eventThreshold; omega
    have h' : (m : ℝ) ≤ 4 * (eventThreshold m : ℝ) + 4 := by exact_mod_cast this
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hgap : (m : ℝ) * (1 / 4 - TensorCHSH.chshErrRate)
      ≤ (eventThreshold m : ℝ) + 1 - m * TensorCHSH.chshErrRate := by linarith
  have hgap0 : 0 < (m : ℝ) * (1 / 4 - TensorCHSH.chshErrRate) := mul_pos hm0 (by linarith)
  have hk : (m : ℝ) * TensorCHSH.chshErrRate < eventThreshold m + 1 := by linarith
  have h1 := lowTail_ge hkm hr0.le hr1.le hk
  have hc : m * TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate)
        / ((eventThreshold m + 1) - m * TensorCHSH.chshErrRate) ^ 2
      ≤ TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate)
        / (m * (1 / 4 - TensorCHSH.chshErrRate) ^ 2) := by
    rw [div_le_div_iff₀ (pow_pos (hgap0.trans_le hgap) 2) (mul_pos hm0 (pow_pos (by linarith) 2))]
    have hsq := pow_le_pow_left₀ hgap0.le hgap 2
    have hnum : 0 ≤ TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate) :=
      mul_nonneg hr0.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hsq hnum]
  unfold tensorTail
  linarith

theorem tensorTail_lt_one {m : ℕ} (hm : 1 ≤ m) : tensorTail m < 1 :=
  lowTail_lt_one (by unfold eventThreshold; omega)

theorem tensorTail_pos (m : ℕ) : 0 < tensorTail m := by
  unfold tensorTail
  have hr0 := chshErrRate_pos
  have hr1 := chshErrRate_lt_one
  refine Finset.sum_pos' (fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hr0.le _))) ⟨0, by simp, ?_⟩
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, mul_one, Nat.sub_zero]
  exact pow_pos (by linarith) _

theorem tendsto_tensorTail : Tendsto tensorTail atTop (𝓝 1) := by
  have hc := tendsto_const_div_atTop_nhds_zero_nat
    (TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate) / (1 / 4 - TensorCHSH.chshErrRate) ^ 2)
  have hlow : Tendsto (fun m : ℕ => 1 - TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate)
      / (1 / 4 - TensorCHSH.chshErrRate) ^ 2 / m) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have h := tensorTail_ge hm
    have e : TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate)
        / (1 / 4 - TensorCHSH.chshErrRate) ^ 2 / m
        = TensorCHSH.chshErrRate * (1 - TensorCHSH.chshErrRate)
          / (m * (1 / 4 - TensorCHSH.chshErrRate) ^ 2) := by
      rw [div_div, mul_comm ((1 / 4 - TensorCHSH.chshErrRate) ^ 2)]
    rw [e]
    exact h
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact (tensorTail_lt_one hm).le

/-- **Theorem A.4, PVM part (tensor family).** For every input law `μ`,
`sup_m S_μ(T_m) = Ξ(μ)`. -/
theorem iSup_statStrength_tensorCHSHTable {μ : Fin 2 → Fin 2 → ℝ} (hμ : ∀ x y, 0 ≤ μ x y)
    (hμ1 : ∑ x, ∑ y, μ x y = 1) :
    ⨆ m : ℕ, statStrength μ (TensorCHSH.tensorCHSHTable m) = xiMin μ := by
  have hle : ∀ m, statStrength μ (TensorCHSH.tensorCHSHTable m) ≤ xiMin μ := fun m =>
    (statistical_ceiling_spec (TensorCHSH.tensorCHSHTable_isNoSignalling m) hμ hμ1).1.trans
      (statistical_ceiling_spec (TensorCHSH.tensorCHSHTable_isNoSignalling m) hμ hμ1).2
  refine le_antisymm (iSup_le hle) ?_
  have hfin : xiMin μ ≠ ∞ := xiMin_ne_top hμ hμ1
  have hYfin : (⨆ m : ℕ, statStrength μ (TensorCHSH.tensorCHSHTable m)) ≠ ∞ :=
    ne_top_of_le_ne_top hfin (iSup_le hle)
  have hr0 := chshErrRate_pos
  have hr1 := chshErrRate_lt_one
  -- the real inequality `t_m Ξ ≤ Y + h₂(t_m)` for every `m ≥ 1`
  have key : ∀ m : ℕ, 1 ≤ m → tensorTail m * (xiMin μ).toReal
      ≤ (⨆ m : ℕ, statStrength μ (TensorCHSH.tensorCHSHTable m)).toReal
        + Real.binEntropy (tensorTail m) / Real.log 2 := by
    intro m hm
    have hk : 4 * eventThreshold m < m := by unfold eventThreshold; omega
    have hev : ∀ x y, TensorCHSH.eventProb (eventThreshold m)
        (TensorCHSH.tensorTable m TensorCHSH.chshErrRate) x y = tensorTail m := fun x y =>
      eventProb_tensorTable m _ (by unfold eventThreshold; omega) _ x y
    have h := TensorCHSH.mul_xiMin_le_statStrength_add hk
      (tensorTable_isBehaviour m hr0.le hr1.le) (tensorTail_pos m) (tensorTail_lt_one hm) hev hμ hμ1
    rw [← TensorCHSH.tensorCHSHTable_eq] at h
    have h2 := h.trans (add_le_add
      (le_iSup (fun m => statStrength μ (TensorCHSH.tensorCHSHTable m)) m) le_rfl)
    have hh0 : 0 ≤ Real.binEntropy (tensorTail m) / Real.log 2 :=
      div_nonneg (Real.binEntropy_nonneg (tensorTail_pos m).le (tensorTail_lt_one hm).le)
        (Real.log_pos (by norm_num)).le
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hYfin,
      ← ENNReal.ofReal_mul (tensorTail_pos m).le, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hh0]
      at h2
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg ENNReal.toReal_nonneg hh0)).mp h2
  have hlim1 : Tendsto (fun m => tensorTail m * (xiMin μ).toReal) atTop
      (𝓝 (1 * (xiMin μ).toReal)) := tendsto_tensorTail.mul_const _
  have hlim2 : Tendsto (fun m => (⨆ m : ℕ, statStrength μ (TensorCHSH.tensorCHSHTable m)).toReal
      + Real.binEntropy (tensorTail m) / Real.log 2) atTop
      (𝓝 ((⨆ m : ℕ, statStrength μ (TensorCHSH.tensorCHSHTable m)).toReal
        + Real.binEntropy 1 / Real.log 2)) :=
    tendsto_const_nhds.add (((Real.binEntropy_continuous.tendsto 1).comp tendsto_tensorTail).div_const _)
  have hX := le_of_tendsto_of_tendsto hlim1 hlim2 (eventually_atTop.mpr ⟨1, key⟩)
  rw [one_mul, Real.binEntropy_one, zero_div, add_zero] at hX
  exact (ENNReal.toReal_le_toReal hfin hYfin).mp hX

end

end CGLMPBounds
