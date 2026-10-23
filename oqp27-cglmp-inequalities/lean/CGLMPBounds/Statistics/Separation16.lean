module

public import CGLMPBounds.Statistics.EventBound
public import CGLMPBounds.Statistics.FourierBound
public import CGLMPBounds.Certificates.TableF1
public import CGLMPBounds.TensorCHSH.Measurement
public import CGLMPBounds.Noise.Separation

@[expose] public section


/-!
# The explicit statistical separation (F.16)

Supplement, Appendix F.5: "At `m = 41`, exact binomial summation gives
`t_41 = Pr{Bin(41, r) ≤ 10} > p := 606/625 > 3/4`. [...] Since `D_bin(t‖3/4)` increases for
`t > 3/4`, it remains to bound `D_bin(p‖3/4)`. [...] The left side therefore bounds
`ln(2) D_bin(p‖3/4) - (9/14) ln(4/3)` from below. Combining with (F.7) and (F.15) gives, for every
`m ≥ 41`, `S_unif(T_m) > (9/14) log₂(4/3) > (16/25) log₂(4/3) > sup_μ S_μ(Q_{2^m})`."

The logarithms are bounded with the Taylor remainder bound of `Real.abs_log_sub_add_sum_range_le`
and `Real.log_two_lt_d9`, instead of the supplement's atanh series; the margin is the same order
(`> 10⁻⁵`).
-/

namespace CGLMPBounds

noncomputable section

open scoped ENNReal
open Finset

/-- `T_m` is a behaviour (binomial theorem). -/
theorem tensorTable_isBehaviour (m : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    IsBehaviour (TensorCHSH.tensorTable m ρ) where
  nonneg := tensorTable_nonneg hρ0 hρ1
  sum_eq_one x y := by
    have h := TensorCHSH.sum_sum_tensorTable (m := m) ρ (fun _ => 1) x y
    simp only [one_mul] at h
    rw [h]
    calc ∑ j ∈ range (m + 1), (m.choose j : ℝ) * ((1 - ρ) ^ (m - j) * ρ ^ j)
        = ∑ j ∈ range (m + 1), ρ ^ j * (1 - ρ) ^ (m - j) * (m.choose j : ℝ) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = (ρ + (1 - ρ)) ^ m := (add_pow ρ (1 - ρ) m).symm
      _ = 1 := by ring

theorem chshErrRate_pos : 0 < TensorCHSH.chshErrRate := by
  unfold TensorCHSH.chshErrRate
  have h : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

theorem chshErrRate_lt_one : TensorCHSH.chshErrRate < 1 := by
  unfold TensorCHSH.chshErrRate
  have := Real.sqrt_nonneg 2
  linarith

/-- The event probability of `T_m` is the binomial lower tail. -/
theorem eventProb_tensorTable (m k : ℕ) (hk : k ≤ m) (ρ : ℝ) (x y : Fin 2) :
    TensorCHSH.eventProb k (TensorCHSH.tensorTable m ρ) x y
      = ∑ j ∈ range (k + 1), (m.choose j : ℝ) * ((1 - ρ) ^ (m - j) * ρ ^ j) := by
  have h := TensorCHSH.sum_sum_tensorTable (m := m) ρ (fun j => if j ≤ k then (1 : ℝ) else 0) x y
  have e : ∀ j ∈ range (m + 1), (m.choose j : ℝ) * ((if j ≤ k then (1 : ℝ) else 0)
      * ((1 - ρ) ^ (m - j) * ρ ^ j))
      = if j ≤ k then (m.choose j : ℝ) * ((1 - ρ) ^ (m - j) * ρ ^ j) else 0 := by
    intro j _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, Certificates.lowSum_filter m k hk] at h
  exact h

/-- The binomial lower tail `Pr{Bin(m, r) ≤ k}` is `< 1` for `k < m`. -/
theorem lowTail_lt_one {m k : ℕ} (hk : k < m) :
    ∑ j ∈ range (k + 1), (m.choose j : ℝ)
        * ((1 - TensorCHSH.chshErrRate) ^ (m - j) * TensorCHSH.chshErrRate ^ j) < 1 := by
  have hr0 := chshErrRate_pos
  have hr1 := chshErrRate_lt_one
  have hpos : ∀ j ∈ range (m + 1), 0 < (m.choose j : ℝ)
      * ((1 - TensorCHSH.chshErrRate) ^ (m - j) * TensorCHSH.chshErrRate ^ j) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hjm))
      (mul_pos (pow_pos (sub_pos.mpr hr1) _) (pow_pos hr0 _))
  have htot : ∑ j ∈ range (m + 1), (m.choose j : ℝ)
      * ((1 - TensorCHSH.chshErrRate) ^ (m - j) * TensorCHSH.chshErrRate ^ j) = 1 := by
    have h := (tensorTable_isBehaviour m hr0.le hr1.le).sum_eq_one 0 0
    have h2 := TensorCHSH.sum_sum_tensorTable (m := m) TensorCHSH.chshErrRate (fun _ => 1) 0 0
    simp only [one_mul] at h2
    rw [← h2, h]
  exact (Finset.sum_lt_sum_of_subset
    (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)) (i := m)
    (Finset.mem_range.mpr (by omega)) (by rw [Finset.mem_range]; omega)
    (hpos m (Finset.mem_range.mpr (by omega))) (fun j hj _ => (hpos j hj).le)).trans_eq htot

namespace Certificates

/-- `625 · 4^41 t_41 - 606 · 4^41` as an element of `ℤ[√2]`. -/
def t41Data : ℤ√2 :=
  625 * ((⟨2, 1⟩ : ℤ√2) ^ (41 - 2 * 10) * (horner 41 ((⟨2, 1⟩ : ℤ√2) ^ 2) 10).1)
    - ⟨606 * 4 ^ 41, 0⟩

theorem t41Data_pos : posZS t41Data.re t41Data.im = true := by
  decide +kernel

/-- (F.16): `t_41 = Pr{Bin(41, r) ≤ 10} > 606/625`. -/
theorem t41_gt : (606 : ℝ) / 625 < ∑ j ∈ range (10 + 1),
    ((41 : ℕ).choose j : ℝ) * ((1 - TensorCHSH.chshErrRate) ^ (41 - j)
      * TensorCHSH.chshErrRate ^ j) := by
  have hD := posZS_sound _ _ t41Data_pos
  rw [← toReal_apply] at hD
  have hval : toReal t41Data = 625 * ((4 : ℝ) ^ 41 * ∑ j ∈ range (10 + 1),
      ((41 : ℕ).choose j : ℝ) * ((1 - TensorCHSH.chshErrRate) ^ (41 - j)
        * TensorCHSH.chshErrRate ^ j)) - 606 * 4 ^ 41 := by
    rw [lowSum_tensor 41 10 (by norm_num)]
    unfold t41Data
    rw [map_sub, map_mul, toReal_apply ⟨606 * 4 ^ 41, 0⟩]
    push_cast
    simp only [map_ofNat]
    ring
  rw [hval] at hD
  have h4 : (0 : ℝ) < 4 ^ 41 := by positivity
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 625)]
  have key : (606 : ℝ) * 4 ^ 41 < ((∑ j ∈ range (10 + 1), ((41 : ℕ).choose j : ℝ)
      * ((1 - TensorCHSH.chshErrRate) ^ (41 - j) * TensorCHSH.chshErrRate ^ j)) * 625) * 4 ^ 41 := by
    linarith
  exact lt_of_mul_lt_mul_right key h4.le

end Certificates

/-- `t ↦ D_bin(t‖z)` (in nats) is nondecreasing for `t ≥ z`. -/
theorem binKL_mono {z p t : ℝ} (hz : 0 < z) (hz1 : z < 1) (hp : z < p) (hpt : p ≤ t)
    (ht1 : t < 1) :
    p * Real.log (p / z) + (1 - p) * Real.log ((1 - p) / (1 - z))
      ≤ t * Real.log (t / z) + (1 - t) * Real.log ((1 - t) / (1 - z)) := by
  have hp0 : 0 < p := hz.trans hp
  have ht0 : 0 < t := hp0.trans_le hpt
  have hp1 : p < 1 := hpt.trans_lt ht1
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos ht0 hp0)
  have h2 := Real.one_sub_inv_le_log_of_pos (div_pos (sub_pos.mpr ht1) (sub_pos.mpr hp1))
  rw [inv_div, Real.log_div ht0.ne' hp0.ne'] at h1
  rw [inv_div, Real.log_div (sub_pos.mpr ht1).ne' (sub_pos.mpr hp1).ne'] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 ht0.le
  have h2' := mul_le_mul_of_nonneg_left h2 (sub_pos.mpr ht1).le
  have e1 : t * (1 - p / t) = t - p := by
    rw [mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ ht0.ne']
  have e2 : (1 - t) * (1 - (1 - p) / (1 - t)) = p - t := by
    rw [mul_sub, mul_one, mul_div_assoc', mul_div_cancel_left₀ _ (sub_pos.mpr ht1).ne']
    ring
  rw [e1] at h1'
  rw [e2] at h2'
  have hmon : Real.log ((1 - p) / (1 - z)) ≤ Real.log (p / z) := by
    have a1 : (1 - p) / (1 - z) < 1 := (div_lt_one (sub_pos.mpr hz1)).mpr (by linarith)
    have a2 : 1 < p / z := (one_lt_div hz).mpr hp
    exact Real.log_le_log (div_pos (sub_pos.mpr hp1) (sub_pos.mpr hz1)) (a1.le.trans a2.le)
  have hmon' := mul_le_mul_of_nonneg_left hmon (sub_nonneg.mpr hpt)
  rw [Real.log_div hp0.ne' hz.ne', Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr hz1).ne']
    at hmon'
  rw [Real.log_div hp0.ne' hz.ne', Real.log_div ht0.ne' hz.ne',
    Real.log_div (sub_pos.mpr hp1).ne' (sub_pos.mpr hz1).ne',
    Real.log_div (sub_pos.mpr ht1).ne' (sub_pos.mpr hz1).ne']
  nlinarith [h1', h2', hmon']

theorem log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    -(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg hx0]; exact hx1) n
  rw [abs_of_nonneg hx0] at h
  have h' := (abs_le.mp h).1
  linarith

theorem neg_log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ -Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le (show |x| < 1 by rw [abs_of_nonneg hx0]; exact hx1) n
  rw [abs_of_nonneg hx0] at h
  have h' := (abs_le.mp h).2
  linarith

/-- (F.16): `ln(2) D_bin(606/625 ‖ 3/4) > (9/14) ln(4/3)`. -/
theorem binKL_p_gt : (9 / 14 : ℝ) * Real.log (4 / 3)
    < 606 / 625 * Real.log (606 / 625 / (3 / 4))
      + (1 - 606 / 625) * Real.log ((1 - 606 / 625) / (1 - 3 / 4)) := by
  have e1 : Real.log (606 / 625 / (3 / 4)) = Real.log (4 / 3) + Real.log (1 - 19 / 625) := by
    rw [← Real.log_mul (x := 4 / 3) (y := 1 - 19 / 625) (by norm_num) (by norm_num)]
    norm_num
  have e2 : Real.log ((1 - 606 / 625) / (1 - 3 / 4))
      = Real.log (1 - 17 / 625) - 3 * Real.log 2 := by
    have h : (1 - 606 / 625 : ℝ) / (1 - 3 / 4) = (1 - 17 / 625) / 2 ^ 3 := by norm_num
    rw [h, Real.log_div (x := 1 - 17 / 625) (y := 2 ^ 3) (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have e3 : Real.log (4 / 3) = -Real.log (1 - 1 / 4) := by
    rw [show (1 : ℝ) - 1 / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv, neg_neg]
  have l1 := neg_log_one_sub_ge (x := 1 / 4) (by norm_num) (by norm_num) 10
  have l2 := log_one_sub_ge (x := 19 / 625) (by norm_num) (by norm_num) 4
  have l3 := log_one_sub_ge (x := 17 / 625) (by norm_num) (by norm_num) 4
  have l4 := Real.log_two_lt_d9
  rw [← e3] at l1
  rw [e1, e2]
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (4 / 3) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = Real.log (1 - 19 / 625) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Real.log (1 - 17 / 625) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = Real.log 2 := ⟨_, rfl⟩
  rw [← hL] at l1 ⊢
  rw [← hA] at l2 ⊢
  rw [← hB] at l3 ⊢
  rw [← hT] at l4 ⊢
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at l1 l2 l3
  norm_num at l1 l2 l3 l4 ⊢
  linarith

/-- (F.16), lower half: `S_unif(T_m) > (9/14) log₂(4/3)` for every `m ≥ 41`. -/
theorem statStrength_tensorTable_gt (m : ℕ) (hm : 41 ≤ m) :
    ENNReal.ofReal (9 / 14 * cKL)
      < statStrength (fun _ _ => 1 / 4) (TensorCHSH.tensorTable m TensorCHSH.chshErrRate) := by
  have hr0 := chshErrRate_pos
  have hr1 := chshErrRate_lt_one
  set t := ∑ j ∈ range (10 + 1), ((41 : ℕ).choose j : ℝ)
    * ((1 - TensorCHSH.chshErrRate) ^ (41 - j) * TensorCHSH.chshErrRate ^ j) with ht
  have ht_gt : (606 : ℝ) / 625 < t := Certificates.t41_gt
  have ht1 : t < 1 := lowTail_lt_one (by norm_num)
  have hev : ∀ x y, TensorCHSH.eventProb 10 (TensorCHSH.tensorTable 41 TensorCHSH.chshErrRate) x y
      = t := fun x y => eventProb_tensorTable 41 10 (by norm_num) _ x y
  have hS41 := TensorCHSH.binRelEntropy_le_statStrength (m := 41) (k := 10) (by norm_num)
    (tensorTable_isBehaviour 41 hr0.le hr1.le) (by linarith) ht1 hev
  have hmono := statStrength_tensorTable_le (fun _ _ => 1 / 4) hm hr0.le hr1.le
  refine lt_of_lt_of_le ?_ (hS41.trans hmono)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [binRelEntropy_of_mem (t := t) (z := 3 / 4) (by norm_num) (by norm_num)]
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos (by norm_num) cKL_pos).le).mpr ?_
  have hmono' := binKL_mono (z := 3 / 4) (p := 606 / 625) (t := t) (by norm_num) (by norm_num)
    (by norm_num) ht_gt.le ht1
  have hbits : ∀ s : ℝ, s * Real.logb 2 (s / (3 / 4)) + (1 - s) * Real.logb 2 ((1 - s) / (1 - 3 / 4))
      = (s * Real.log (s / (3 / 4)) + (1 - s) * Real.log ((1 - s) / (1 - 3 / 4))) / Real.log 2 := by
    intro s
    unfold Real.logb
    ring
  rw [hbits]
  unfold cKL Real.logb
  rw [mul_div_assoc']
  exact div_lt_div_of_pos_right (binKL_p_gt.trans_le hmono') hlog2

/-- **(F.16).** For every `m ≥ 41`, the common-input tensor CHSH behaviour with uniform inputs and
the Fourier-phase behaviour on `Φ_{2^m}` satisfy
`S_unif(T_m) > (9/14) log₂(4/3) > (16/25) log₂(4/3) > sup_μ S_μ(Q_{2^m})`. -/
theorem statistical_separation_spec (m : ℕ) (hm : 41 ≤ m) :
    ENNReal.ofReal (9 / 14 * cKL)
        < statStrength (fun _ _ => 1 / 4) (TensorCHSH.tensorCHSHTable m) ∧
      (16 / 25 : ℝ) * cKL < 9 / 14 * cKL ∧
      (⨆ μ ∈ {μ : Fin 2 → Fin 2 → ℝ | (∀ x y, 0 ≤ μ x y) ∧ ∑ x, ∑ y, μ x y = 1},
          statStrength μ (fourierTable (2 ^ m))) < ENNReal.ofReal (16 / 25 * cKL) := by
  refine ⟨?_, mul_lt_mul_of_pos_right (by norm_num) cKL_pos, ?_⟩
  · rw [TensorCHSH.tensorCHSHTable_eq]
    exact statStrength_tensorTable_gt m hm
  · have h2 : 2 ≤ 2 ^ m := two_le_two_pow (by omega)
    exact iSup_statStrength_fourierTable_lt (2 ^ m) h2

end

end CGLMPBounds
