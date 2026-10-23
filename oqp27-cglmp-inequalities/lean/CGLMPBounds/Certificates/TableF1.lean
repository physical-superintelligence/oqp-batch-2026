module

public import CGLMPBounds.TensorCHSH.WitnessValue

@[expose] public section


/-!
# Exact certificates for Table F.1, rows `M = 955` and `M = 1182`

Supplement, proof of Theorem A.3 and Table F.1: with `M = 955`, `k = 152`, `h = M - 3k = 499`,
`G_{M,k}(T_M) > q₀ = 8757/10000` and `G_{M,k}(u) > -b₀ = -871/10000`; at `v₀ = 3049/5000`,
`v₀ q₀ - (1 - v₀) b₀ > 1/2`, hence `v_crit(T_M) < v₀`.

The binomial tails are evaluated exactly in `ℤ[√2]` (`x = 2 + √2 = 4(1-r)`, `y = 2 - √2 = 4r`,
`xy = 2`) by a Horner scheme whose correctness is proved here; the two resulting integer
comparisons are checked by the kernel with `decide +kernel` (no axioms beyond the standard three).
Statements are about the closed-formula table `tensorTable m chshErrRate` of (F.5).
-/

namespace CGLMPBounds.Certificates

open Finset TensorCHSH

/-! ### Horner evaluation in `ℤ[√2]` -/

/-- `(acc, c)` after `n` steps: `c = C(M,n) 2^n`, `acc = Σ_{j ≤ n} C(M,j) 2^j z^{n-j}`. -/
def horner (M : ℕ) (z : ℤ√2) : ℕ → ℤ√2 × ℕ
  | 0 => (1, 1)
  | n + 1 =>
    let p := horner M z n
    let c := p.2 * 2 * (M - n) / (n + 1)
    (p.1 * z + ⟨(c : ℤ), 0⟩, c)

theorem horner_snd (M : ℕ) (z : ℤ√2) : ∀ n, (horner M z n).2 = M.choose n * 2 ^ n
  | 0 => by simp [horner]
  | n + 1 => by
    show (horner M z n).2 * 2 * (M - n) / (n + 1) = M.choose (n + 1) * 2 ^ (n + 1)
    rw [horner_snd M z n]
    have h := Nat.choose_succ_right_eq M n
    have e : M.choose n * 2 ^ n * 2 * (M - n) = M.choose (n + 1) * 2 ^ (n + 1) * (n + 1) := by
      calc M.choose n * 2 ^ n * 2 * (M - n) = 2 ^ (n + 1) * (M.choose n * (M - n)) := by ring
        _ = 2 ^ (n + 1) * (M.choose (n + 1) * (n + 1)) := by rw [← h]
        _ = M.choose (n + 1) * 2 ^ (n + 1) * (n + 1) := by ring
    rw [e]
    exact Nat.mul_div_cancel _ (Nat.succ_pos n)

theorem horner_fst (M : ℕ) (z : ℤ√2) : ∀ n, (horner M z n).1
    = ∑ j ∈ range (n + 1), (((M.choose j * 2 ^ j : ℕ) : ℤ√2)) * z ^ (n - j)
  | 0 => by simp [horner]
  | n + 1 => by
    have hc : (horner M z n).2 * 2 * (M - n) / (n + 1) = M.choose (n + 1) * 2 ^ (n + 1) :=
      horner_snd M z (n + 1)
    show (horner M z n).1 * z
        + ⟨(((horner M z n).2 * 2 * (M - n) / (n + 1) : ℕ) : ℤ), 0⟩ = _
    rw [hc, horner_fst M z n, ← Zsqrtd.natCast_val, Finset.sum_range_succ _ (n + 1),
      Nat.sub_self, pow_zero, mul_one, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    rw [mul_assoc, ← pow_succ, show n + 1 - j = n - j + 1 by omega]

/-- Low binomial tail through Horner: `Σ_{j ≤ k} C(M,j) x^{M-j} y^j = x^{M-2k} Σ_{j≤k} C(M,j) 2^j
(x²)^{k-j}` when `xy = 2` and `2k ≤ M`. -/
theorem lowTail_eq (M k : ℕ) (hk : 2 * k ≤ M) (x y : ℤ√2) (hxy : x * y = 2) :
    ∑ j ∈ range (k + 1), ((M.choose j : ℕ) : ℤ√2) * (x ^ (M - j) * y ^ j)
      = x ^ (M - 2 * k) * (horner M (x ^ 2) k).1 := by
  rw [horner_fst, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  have hp : x ^ j * y ^ j = 2 ^ j := by rw [← mul_pow, hxy]
  rw [show M - j = (M - 2 * k) + 2 * (k - j) + j by omega, pow_add, pow_add, pow_mul]
  push_cast
  linear_combination (((M.choose j : ℕ) : ℤ√2) * x ^ (M - 2 * k) * (x ^ 2) ^ (k - j)) * hp

/-! ### The real embedding and a sign test -/

/-- `ℤ[√2] → ℝ`, `a + b√2 ↦ a + b√2`. -/
noncomputable def toReal : ℤ√2 →+* ℝ :=
  Zsqrtd.lift ⟨Real.sqrt 2, by rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num⟩

theorem toReal_apply (a : ℤ√2) : toReal a = a.re + a.im * Real.sqrt 2 := rfl

theorem toReal_x : toReal ⟨2, 1⟩ = 4 * (1 - chshErrRate) := by
  rw [toReal_apply]
  unfold chshErrRate
  push_cast
  ring

theorem toReal_y : toReal ⟨2, -1⟩ = 4 * chshErrRate := by
  rw [toReal_apply]
  unfold chshErrRate
  push_cast
  ring

/-- Sign test for `P + Q√2 > 0` on integers. -/
def posZS (P Q : ℤ) : Bool :=
  if 0 ≤ P ∧ 0 ≤ Q then decide (0 < P ∨ 0 < Q)
  else if 0 ≤ P then decide (2 * Q * Q < P * P)
  else if 0 ≤ Q then decide (P * P < 2 * Q * Q)
  else false

theorem posZS_sound (P Q : ℤ) (h : posZS P Q = true) : 0 < (P : ℝ) + Q * Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold posZS at h
  split_ifs at h with h1 h2 h3
  · have h' : 0 < P ∨ 0 < Q := of_decide_eq_true h
    have hP : (0 : ℝ) ≤ P := by exact_mod_cast h1.1
    have hQ : (0 : ℝ) ≤ Q := by exact_mod_cast h1.2
    rcases h' with hP' | hQ'
    · have : (0 : ℝ) < P := by exact_mod_cast hP'
      nlinarith [mul_nonneg hQ hs.le]
    · have : (0 : ℝ) < Q := by exact_mod_cast hQ'
      nlinarith [mul_pos this hs]
  · have h' : 2 * Q * Q < P * P := of_decide_eq_true h
    have hP : (0 : ℝ) ≤ P := by exact_mod_cast h2
    have hQ : (Q : ℝ) < 0 := by
      have : ¬ (0 ≤ Q) := fun hq => h1 ⟨h2, hq⟩
      exact_mod_cast (not_le.mp this)
    have hR : (2 : ℝ) * Q * Q < P * P := by exact_mod_cast h'
    have hprod : 0 < ((P : ℝ) + Q * Real.sqrt 2) * ((P : ℝ) - Q * Real.sqrt 2) := by
      have e : ((P : ℝ) + Q * Real.sqrt 2) * ((P : ℝ) - Q * Real.sqrt 2)
          = P * P - Q * Q * (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [e, hs2]
      linarith
    have hneg : 0 < (P : ℝ) - Q * Real.sqrt 2 := by
      have := mul_pos (neg_pos.mpr hQ) hs
      linarith
    exact (pos_iff_pos_of_mul_pos hprod).mpr hneg
  · have h' : P * P < 2 * Q * Q := of_decide_eq_true h
    have hP : (P : ℝ) < 0 := by exact_mod_cast (not_le.mp h2)
    have hQ : (0 : ℝ) ≤ Q := by exact_mod_cast h3
    have hR : (P : ℝ) * P < 2 * Q * Q := by exact_mod_cast h'
    have hprod : 0 < ((P : ℝ) + Q * Real.sqrt 2) * (Q * Real.sqrt 2 - P) := by
      have e : ((P : ℝ) + Q * Real.sqrt 2) * (Q * Real.sqrt 2 - P)
          = Q * Q * (Real.sqrt 2 * Real.sqrt 2) - P * P := by ring
      rw [e, hs2]
      linarith
    have hpos : 0 < (Q : ℝ) * Real.sqrt 2 - P := by
      have := mul_nonneg hQ hs.le
      linarith
    exact (pos_iff_pos_of_mul_pos hprod).mpr hpos

/-! ### Splitting the witness value into binomial tails -/

theorem four_pow_mul_term (M j : ℕ) (hj : j ≤ M) (a b : ℝ) :
    (4 : ℝ) ^ M * (a ^ (M - j) * b ^ j) = (4 * a) ^ (M - j) * (4 * b) ^ j := by
  rw [mul_pow, mul_pow, show (4 : ℝ) ^ M = 4 ^ (M - j) * 4 ^ j by
    rw [← pow_add, Nat.sub_add_cancel hj]]
  ring

theorem lowSum_filter (M k : ℕ) (hk : k ≤ M) (f : ℕ → ℝ) :
    ∑ j ∈ range (M + 1), (if j ≤ k then f j else 0) = ∑ j ∈ range (k + 1), f j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem highSum_reflect (M h : ℕ) (hh : h ≤ M) (f : ℕ → ℝ) :
    ∑ j ∈ range (M + 1), (if h ≤ j then f j else 0) = ∑ j ∈ range (M - h + 1), f (M - j) := by
  rw [← Finset.sum_range_reflect]
  have e : ∀ j ∈ range (M + 1), (if h ≤ M + 1 - 1 - j then f (M + 1 - 1 - j) else 0)
      = if j ≤ M - h then f (M - j) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show M + 1 - 1 - j = M - j by omega]
    by_cases h1 : j ≤ M - h
    · rw [if_pos (by omega), if_pos h1]
    · rw [if_neg (by omega), if_neg h1]
  rw [Finset.sum_congr rfl e, lowSum_filter M (M - h) (by omega) (fun j => f (M - j))]

/-- `G_{M,k}` as low tail minus high tail. -/
theorem tailDiff_split (M k h : ℕ) (ρ : ℝ) (hk : k ≤ M) (hh : h ≤ M) :
    tailDiff M k h ρ
      = ∑ j ∈ range (k + 1), (M.choose j : ℝ) * ((1 - ρ) ^ (M - j) * ρ ^ j)
        - ∑ j ∈ range (M - h + 1), (M.choose j : ℝ) * (ρ ^ (M - j) * (1 - ρ) ^ j) := by
  unfold tailDiff
  have e : ∀ j ∈ range (M + 1), (M.choose j : ℝ) * (((if j ≤ k then (1 : ℝ) else 0)
        - (if h ≤ j then (1 : ℝ) else 0)) * ((1 - ρ) ^ (M - j) * ρ ^ j))
      = (if j ≤ k then (M.choose j : ℝ) * ((1 - ρ) ^ (M - j) * ρ ^ j) else 0)
        - (if h ≤ j then (M.choose j : ℝ) * ((1 - ρ) ^ (M - j) * ρ ^ j) else 0) := by
    intro j _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, lowSum_filter M k hk,
    highSum_reflect M h hh]
  congr 1
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ M := by have := Finset.mem_range.mp hj; omega
  rw [Nat.choose_symm hj', Nat.sub_sub_self hj']
  ring

theorem lowSum_tensor (M k : ℕ) (hk : 2 * k ≤ M) :
    (4 : ℝ) ^ M * ∑ j ∈ range (k + 1),
        (M.choose j : ℝ) * ((1 - chshErrRate) ^ (M - j) * chshErrRate ^ j)
      = toReal ((⟨2, 1⟩ : ℤ√2) ^ (M - 2 * k) * (horner M ((⟨2, 1⟩ : ℤ√2) ^ 2) k).1) := by
  rw [← lowTail_eq M k hk ⟨2, 1⟩ ⟨2, -1⟩ (by decide), map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ M := by have := Finset.mem_range.mp hj; omega
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, toReal_x, toReal_y, mul_left_comm,
    four_pow_mul_term M j hj']

theorem highSum_tensor (M h : ℕ) (hh : M ≤ 2 * h) (hhM : h ≤ M) :
    (4 : ℝ) ^ M * ∑ j ∈ range (M - h + 1),
        (M.choose j : ℝ) * (chshErrRate ^ (M - j) * (1 - chshErrRate) ^ j)
      = toReal ((⟨2, -1⟩ : ℤ√2) ^ (M - 2 * (M - h))
          * (horner M ((⟨2, -1⟩ : ℤ√2) ^ 2) (M - h)).1) := by
  rw [← lowTail_eq M (M - h) (by omega) ⟨2, -1⟩ ⟨2, 1⟩ (by decide), map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ M := by have := Finset.mem_range.mp hj; omega
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, toReal_y, toReal_x, mul_left_comm,
    four_pow_mul_term M j hj']

/-! ### Row `M = 955` of Table F.1 -/

/-- `10000 · 4^955 G_{955,152}(T_955) - 8757 · 4^955` as an element of `ℤ[√2]`. -/
def tensorTailData : ℤ√2 :=
  10000 * ((⟨2, 1⟩ : ℤ√2) ^ (955 - 2 * 152) * (horner 955 ((⟨2, 1⟩ : ℤ√2) ^ 2) 152).1
      - (⟨2, -1⟩ : ℤ√2) ^ (955 - 2 * (955 - 499))
        * (horner 955 ((⟨2, -1⟩ : ℤ√2) ^ 2) (955 - 499)).1)
    - ⟨8757 * 4 ^ 955, 0⟩

theorem tensorTailData_pos : posZS tensorTailData.re tensorTailData.im = true := by
  decide +kernel

/-- Table F.1, `M = 955`: `G_{955,152}(T_955) > 8757/10000`. -/
theorem tailDiff_tensor_955 :
    (8757 : ℝ) / 10000 < tailDiff 955 152 499 chshErrRate := by
  have hD := posZS_sound _ _ tensorTailData_pos
  rw [← toReal_apply] at hD
  have hval : toReal tensorTailData
      = 10000 * ((4 : ℝ) ^ 955 * tailDiff 955 152 499 chshErrRate) - 8757 * 4 ^ 955 := by
    rw [tailDiff_split 955 152 499 chshErrRate (by norm_num) (by norm_num), mul_sub,
      lowSum_tensor 955 152 (by norm_num), highSum_tensor 955 499 (by norm_num) (by norm_num)]
    unfold tensorTailData
    rw [map_sub, map_mul, map_sub, toReal_apply ⟨8757 * 4 ^ 955, 0⟩]
    push_cast
    simp only [map_ofNat]
    ring
  rw [hval] at hD
  have h4 : (0 : ℝ) < 4 ^ 955 := by positivity
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 10000)]
  have key : (8757 : ℝ) * 4 ^ 955 < (tailDiff 955 152 499 chshErrRate * 10000) * 4 ^ 955 := by
    linarith
  exact lt_of_mul_lt_mul_right key h4.le

/-- `Σ_{j ≤ n} C(M, j) · 2^n` via Horner at `z = 2`. -/
theorem horner_two_fst (M n : ℕ) :
    (horner M 2 n).1 = (((2 ^ n * ∑ j ∈ range (n + 1), M.choose j : ℕ) : ℤ√2)) := by
  rw [horner_fst, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [show (2 : ℤ√2) ^ n = 2 ^ (n - j) * 2 ^ j by rw [← pow_add, Nat.sub_add_cancel hj']]
  ring

/-- `2^456 Σ_{j ≤ 456} C(955, j)`, computed by Horner at `z = 2`. -/
def uniformHorner : ℤ := (horner 955 2 (955 - 499)).1.re

/-- The comparison bound `871 · 2^955 · 2^456`. -/
def uniformBound : ℤ := 871 * 2 ^ 955 * 2 ^ (955 - 499)

/-- `10000 · 2^456 Σ_{j ≤ 456} C(955, j) - 871 · 2^955 · 2^456`, negative by computation. -/
def uniformTailData : ℤ := 10000 * uniformHorner - uniformBound

theorem uniformTailData_neg : decide (uniformTailData < 0) = true := by
  decide +kernel

/-- Table F.1, `M = 955`: `G_{955,152}(u_{2^955}) > -871/10000`. -/
theorem tailDiff_uniform_955 : (-871 : ℝ) / 10000 < tailDiff 955 152 499 (1 / 2) := by
  have h0 : (10000 : ℝ) * (uniformHorner : ℝ) < (uniformBound : ℝ) := by
    have h := of_decide_eq_true uniformTailData_neg
    unfold uniformTailData at h
    have h' : 10000 * uniformHorner < uniformBound := by linarith
    exact_mod_cast h'
  have hre : (uniformHorner : ℝ)
      = 2 ^ (955 - 499) * ∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ) := by
    unfold uniformHorner
    rw [horner_two_fst, Zsqrtd.re_natCast]
    push_cast <;> ring
  have hbound : (uniformBound : ℝ) = 871 * 2 ^ 955 * 2 ^ (955 - 499) := by
    unfold uniformBound
    push_cast <;> ring
  rw [hre, hbound] at h0
  rw [tailDiff_split 955 152 499 (1 / 2) (by norm_num) (by norm_num)]
  have hlow : 0 ≤ ∑ j ∈ range (152 + 1), (Nat.choose 955 j : ℝ)
      * ((1 - 1 / 2 : ℝ) ^ (955 - j) * (1 / 2 : ℝ) ^ j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)))
  have hhigh : ∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ)
        * ((1 / 2 : ℝ) ^ (955 - j) * (1 - 1 / 2 : ℝ) ^ j)
      = (1 / 2 : ℝ) ^ 955 * ∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ 955 := by have := Finset.mem_range.mp hj; omega
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← pow_add, Nat.sub_add_cancel hj']
    ring
  rw [hhigh]
  have h2 : (0 : ℝ) < 2 ^ (955 - 499) := by positivity
  have hS' : 10000 * ∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ) < 871 * 2 ^ 955 := by
    nlinarith [h0, h2]
  have hsum : (1 / 2 : ℝ) ^ 955 * ∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ)
      < 871 / 10000 := by
    have e : (1 / 2 : ℝ) ^ 955 * ∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ)
        = (∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ)) / 2 ^ 955 := by
      rw [one_div_pow]
      ring
    rw [e, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hneg' : -(871 / 10000 : ℝ)
      < -((1 / 2 : ℝ) ^ 955 * ∑ j ∈ range (955 - 499 + 1), (Nat.choose 955 j : ℝ)) :=
    neg_lt_neg hsum
  rw [neg_div, sub_eq_add_neg]
  exact lt_of_lt_of_le hneg' (le_add_of_nonneg_left hlow)

/-- **Table F.1, row `M = 955`**: `v_crit(T_955) < 3049/5000` for the closed-formula table. -/
theorem critVisibility_tensorTable_955_lt :
    critVisibility (tensorTable 955 chshErrRate) < 3049 / 5000 := by
  refine critVisibility_tensorTable_lt (k := 152) (by norm_num) (by norm_num) ?_
  have h1 := tailDiff_tensor_955
  have h2 := tailDiff_uniform_955
  norm_num at h1 h2 ⊢
  nlinarith [h1, h2]


/-! ### Row `M = 1182` of Table F.1 -/

/-- `100000 · 4^1182 G_{1182,188}(T_1182) - 89643 · 4^1182` as an element of `ℤ[√2]`. -/
def tensorTailData1182 : ℤ√2 :=
  100000 * ((⟨2, 1⟩ : ℤ√2) ^ (1182 - 2 * 188) * (horner 1182 ((⟨2, 1⟩ : ℤ√2) ^ 2) 188).1
      - (⟨2, -1⟩ : ℤ√2) ^ (1182 - 2 * (1182 - 618))
        * (horner 1182 ((⟨2, -1⟩ : ℤ√2) ^ 2) (1182 - 618)).1)
    - ⟨89643 * 4 ^ 1182, 0⟩

theorem tensorTailData1182_pos : posZS tensorTailData1182.re tensorTailData1182.im = true := by
  decide +kernel

/-- Table F.1, `M = 1182`: `G_{1182,188}(T_1182) > 89643/100000`. -/
theorem tailDiff_tensor_1182 :
    (89643 : ℝ) / 100000 < tailDiff 1182 188 618 chshErrRate := by
  have hD := posZS_sound _ _ tensorTailData1182_pos
  rw [← toReal_apply] at hD
  have hval : toReal tensorTailData1182
      = 100000 * ((4 : ℝ) ^ 1182 * tailDiff 1182 188 618 chshErrRate) - 89643 * 4 ^ 1182 := by
    rw [tailDiff_split 1182 188 618 chshErrRate (by norm_num) (by norm_num), mul_sub,
      lowSum_tensor 1182 188 (by norm_num), highSum_tensor 1182 618 (by norm_num) (by norm_num)]
    unfold tensorTailData1182
    rw [map_sub, map_mul, map_sub, toReal_apply ⟨89643 * 4 ^ 1182, 0⟩]
    push_cast
    simp only [map_ofNat]
    ring
  rw [hval] at hD
  have h4 : (0 : ℝ) < 4 ^ 1182 := by positivity
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 100000)]
  have key : (89643 : ℝ) * 4 ^ 1182 < (tailDiff 1182 188 618 chshErrRate * 100000) * 4 ^ 1182 := by
    linarith
  exact lt_of_mul_lt_mul_right key h4.le

/-- `2^564 Σ_{j ≤ 564} C(1182, j)`, computed by Horner at `z = 2`. -/
def uniformHorner1182 : ℤ := (horner 1182 2 (1182 - 618)).1.re

/-- The comparison bound `6157 · 2^1182 · 2^564`. -/
def uniformBound1182 : ℤ := 6157 * 2 ^ 1182 * 2 ^ (1182 - 618)

/-- `100000 · 2^564 Σ_{j ≤ 564} C(1182, j) - 6157 · 2^1182 · 2^564`, negative by computation. -/
def uniformTailData1182 : ℤ := 100000 * uniformHorner1182 - uniformBound1182

theorem uniformTailData1182_neg : decide (uniformTailData1182 < 0) = true := by
  decide +kernel

/-- Table F.1, `M = 1182`: `G_{1182,188}(u_{2^1182}) > -6157/100000`. -/
theorem tailDiff_uniform_1182 : (-6157 : ℝ) / 100000 < tailDiff 1182 188 618 (1 / 2) := by
  have h0 : (100000 : ℝ) * (uniformHorner1182 : ℝ) < (uniformBound1182 : ℝ) := by
    have h := of_decide_eq_true uniformTailData1182_neg
    unfold uniformTailData1182 at h
    have h' : 100000 * uniformHorner1182 < uniformBound1182 := by linarith
    exact_mod_cast h'
  have hre : (uniformHorner1182 : ℝ)
      = 2 ^ (1182 - 618) * ∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ) := by
    unfold uniformHorner1182
    rw [horner_two_fst, Zsqrtd.re_natCast]
    push_cast <;> ring
  have hbound : (uniformBound1182 : ℝ) = 6157 * 2 ^ 1182 * 2 ^ (1182 - 618) := by
    unfold uniformBound1182
    push_cast <;> ring
  rw [hre, hbound] at h0
  rw [tailDiff_split 1182 188 618 (1 / 2) (by norm_num) (by norm_num)]
  have hlow : 0 ≤ ∑ j ∈ range (188 + 1), (Nat.choose 1182 j : ℝ)
      * ((1 - 1 / 2 : ℝ) ^ (1182 - j) * (1 / 2 : ℝ) ^ j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)))
  have hhigh : ∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ)
        * ((1 / 2 : ℝ) ^ (1182 - j) * (1 - 1 / 2 : ℝ) ^ j)
      = (1 / 2 : ℝ) ^ 1182 * ∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ 1182 := by have := Finset.mem_range.mp hj; omega
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← pow_add, Nat.sub_add_cancel hj']
    ring
  rw [hhigh]
  have h2 : (0 : ℝ) < 2 ^ (1182 - 618) := by positivity
  have hS' : 100000 * ∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ) < 6157 * 2 ^ 1182 := by
    nlinarith [h0, h2]
  have hsum : (1 / 2 : ℝ) ^ 1182 * ∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ)
      < 6157 / 100000 := by
    have e : (1 / 2 : ℝ) ^ 1182 * ∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ)
        = (∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ)) / 2 ^ 1182 := by
      rw [one_div_pow]
      ring
    rw [e, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hneg' : -(6157 / 100000 : ℝ)
      < -((1 / 2 : ℝ) ^ 1182 * ∑ j ∈ range (1182 - 618 + 1), (Nat.choose 1182 j : ℝ)) :=
    neg_lt_neg hsum
  rw [neg_div, sub_eq_add_neg]
  exact lt_of_lt_of_le hneg' (le_add_of_nonneg_left hlow)

/-- **Table F.1, row `M = 1182`**: `v_crit(T_1182) < 3049/5000` for the closed-formula table. -/
theorem critVisibility_tensorTable_1182_lt :
    critVisibility (tensorTable 1182 chshErrRate) < 17 / 29 := by
  refine critVisibility_tensorTable_lt (k := 188) (by norm_num) (by norm_num) ?_
  have h1 := tailDiff_tensor_1182
  have h2 := tailDiff_uniform_1182
  norm_num at h1 h2 ⊢
  nlinarith [h1, h2]

end CGLMPBounds.Certificates
