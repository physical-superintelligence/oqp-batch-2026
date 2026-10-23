module

public import ThreeCopyQutritWerner.CertificateX2PackedCore

@[expose] public section


/-! Packed engine: soundness of `rowBlockCheck`.

`rowBlockCheck_sound`: a passed check gives, for every block `j < q`, the exact signed identity
`∑_{k<n} x_k g_{j,k} = z_j` between the decoded entries of the reversed row `xE`, of the block
operand `GE` and of the compact candidate `zE`. Also: digit bounds from `boundCheck`, digits of
`concatFibers`, and the list version `rowBlockCheckAll_sound`. -/

open scoped BigOperators
open Polynomial

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Dense polynomials -/

/-- The polynomial with coefficients `f 0, ..., f (L-1)`. -/
noncomputable def dpoly (L : ℕ) (f : ℕ → ℤ) : ℤ[X] := ∑ s ∈ Finset.range L, C (f s) * X ^ s

theorem dpoly_coeff (L : ℕ) (f : ℕ → ℤ) (m : ℕ) :
    (dpoly L f).coeff m = if m < L then f m else 0 := by
  unfold dpoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

theorem dpoly_eval (L : ℕ) (f : ℕ → ℤ) (b : ℤ) :
    (dpoly L f).eval b = ∑ s ∈ Finset.range L, f s * b ^ s := by
  unfold dpoly
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem dpoly_natDegree_le (L : ℕ) (f : ℕ → ℤ) : (dpoly L f).natDegree ≤ L - 1 := by
  unfold dpoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  have := Finset.mem_range.mp hs
  exact (Polynomial.natDegree_C_mul_X_pow_le (f s) s).trans (by omega)

theorem dpoly_mul_coeff (n L : ℕ) (f g : ℕ → ℤ) (m : ℕ) :
    (dpoly n f * dpoly L g).coeff m =
      ∑ a ∈ Finset.range (m + 1),
        (if a < n then f a else 0) * (if m - a < L then g (m - a) else 0) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [dpoly_coeff, Nat.succ_eq_add_one]

theorem dpoly_mul_coeff_abs_le (n L : ℕ) (f g : ℕ → ℤ) (X Gb : ℤ)
    (hf : ∀ a < n, |f a| ≤ X) (hg : ∀ b < L, |g b| ≤ Gb) (hX : 0 ≤ X) (hG : 0 ≤ Gb) (m : ℕ) :
    |(dpoly n f * dpoly L g).coeff m| ≤ n * (X * Gb) := by
  rw [dpoly_mul_coeff]
  calc |∑ a ∈ Finset.range (m + 1),
          (if a < n then f a else 0) * (if m - a < L then g (m - a) else 0)|
      ≤ ∑ a ∈ Finset.range (m + 1),
          |(if a < n then f a else 0) * (if m - a < L then g (m - a) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (m + 1), (if a < n then X * Gb else 0) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a < n
        · rw [if_pos ha, if_pos ha, abs_mul]
          by_cases hb : m - a < L
          · rw [if_pos hb]
            exact mul_le_mul (hf a ha) (hg _ hb) (abs_nonneg _) hX
          · rw [if_neg hb, abs_zero, mul_zero]
            exact mul_nonneg hX hG
        · simp [ha]
    _ = ∑ a ∈ (Finset.range (m + 1)).filter (· < n), X * Gb := by
        simp only [Finset.sum_filter]
    _ ≤ ∑ a ∈ Finset.range n, X * Gb := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
          exact ha.2
        · intro _ _ _
          exact mul_nonneg hX hG
    _ = n * (X * Gb) := by
        simp [Finset.sum_const, Finset.card_range]

theorem sum_range_eq_of_zero (N n : ℕ) (hn : n ≤ N) (F : ℕ → ℤ) (hF : ∀ a, n ≤ a → F a = 0) :
    ∑ a ∈ Finset.range N, F a = ∑ a ∈ Finset.range n, F a := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hn)
  intro a _ ha
  exact hF a (by simpa using ha)

theorem dpoly_mul_coeff_middle (n L : ℕ) (f g : ℕ → ℤ) (j : ℕ) (hn : 1 ≤ n)
    (hjL : j * n + n ≤ L) :
    (dpoly n f * dpoly L g).coeff (j * n + (n - 1)) =
      ∑ k ∈ Finset.range n, f (n - 1 - k) * g (j * n + k) := by
  rw [dpoly_mul_coeff]
  have hz : ∀ a, n ≤ a → (if a < n then f a else 0) *
      (if j * n + (n - 1) - a < L then g (j * n + (n - 1) - a) else 0) = 0 := by
    intro a ha
    rw [if_neg (show ¬ a < n by omega), zero_mul]
  rw [sum_range_eq_of_zero (j * n + (n - 1) + 1) n (by omega) _ hz, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [if_pos (show n - 1 - k < n by omega),
    if_pos (show j * n + (n - 1) - (n - 1 - k) < L by omega),
    show j * n + (n - 1) - (n - 1 - k) = j * n + k by omega]

/-! ### Digits of an offset product -/

theorem product_digits (W n L : ℕ) (f g : ℕ → ℤ) (X Gb : ℤ) (hW : 1 ≤ W) (hn : 1 ≤ n)
    (hL : 1 ≤ L) (hf : ∀ a < n, |f a| ≤ X) (hg : ∀ b < L, |g b| ≤ Gb) (hX : 0 ≤ X)
    (hG : 0 ≤ Gb) (hbound : (n : ℤ) * (X * Gb) < 2 ^ (W - 1)) (s : ℕ) (hs : s < n + L) :
    dig W (((dpoly n f * dpoly L g).eval (2 ^ W) + (offset W (W - 1) (n + L) : ℤ)).toNat) s =
      ((dpoly n f * dpoly L g).coeff s + 2 ^ (W - 1)).toNat := by
  have hdeg : (dpoly n f * dpoly L g).natDegree < n + L := by
    have h1 := dpoly_natDegree_le n f
    have h2 := dpoly_natDegree_le L g
    have h3 := Polynomial.natDegree_mul_le (p := dpoly n f) (q := dpoly L g)
    omega
  have hcoef : ∀ i, |(dpoly n f * dpoly L g).coeff i| ≤ n * (X * Gb) :=
    fun i => dpoly_mul_coeff_abs_le n L f g X Gb hf hg hX hG i
  have hB2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hc_cast : ∀ i, ((((dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1)).toNat : ℕ) : ℤ) =
      (dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1) := by
    intro i
    apply Int.toNat_of_nonneg
    have := (abs_le.mp (hcoef i)).1
    linarith
  have hc_lt : ∀ i, ((dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1)).toNat < 2 ^ W := by
    intro i
    have h1 := hc_cast i
    have h2 := (abs_le.mp (hcoef i)).2
    have : ((((dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1)).toNat : ℕ) : ℤ) < 2 ^ W := by
      rw [h1, hB2]
      linarith
    exact_mod_cast this
  have e1 : ((2 ^ (W - 1) * ∑ s ∈ Finset.range (n + L), 2 ^ (W * s) : ℕ) : ℤ) =
      ∑ s ∈ Finset.range (n + L), (2 : ℤ) ^ (W - 1) * (2 ^ W) ^ s := by
    rw [Nat.cast_mul, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [← pow_mul]
    first | (push_cast; ring) | push_cast
  have e2 : ((∑ i ∈ Finset.range (n + L),
        ((dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1)).toNat * (2 ^ W) ^ i : ℕ) : ℤ) =
      ∑ i ∈ Finset.range (n + L),
        ((dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1)) * (2 ^ W) ^ i := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul, hc_cast i]
    first | (push_cast; ring) | push_cast
  have hsum : (dpoly n f * dpoly L g).eval (2 ^ W) + (offset W (W - 1) (n + L) : ℤ) =
      ((∑ i ∈ Finset.range (n + L),
        ((dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1)).toNat * (2 ^ W) ^ i : ℕ) : ℤ) := by
    rw [Polynomial.eval_eq_sum_range' hdeg, offset, repunit_eq W (n + L) hW, e1, e2,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, Int.toNat_natCast]
  unfold dig
  rw [pow_mul]
  exact sum_digit (2 ^ W) (n + L) (fun i => ((dpoly n f * dpoly L g).coeff i + 2 ^ (W - 1)).toNat)
    (by positivity) hc_lt s hs

/-! ### Spreading the compact candidate -/

theorem spread_dig (W n q zE j : ℕ) (hW : 1 ≤ W) (hqn : q + 1 ≤ n) (hz : zE < 2 ^ (W * q))
    (hj : j < q) :
    dig W (zE * repunit (W * (n - 1)) q) (j * n) = dig W zE j := by
  have hn1 : 1 ≤ n - 1 := by omega
  unfold dig
  rw [repunit_eq_pow W (n - 1) q hW hn1, pow_mul 2 W (j * n), pow_mul 2 W j]
  have h := spread_digit (2 ^ W) (n - 1) q zE j (by positivity) (by omega)
    (by rwa [← pow_mul]) hj
  rwa [show n - 1 + 1 = n by omega] at h

/-! ### The main soundness theorem -/

theorem rowBlockCheck_sound (W ox n q xE GE zE : ℕ) (Gb : ℤ)
    (hW : 2 ≤ W) (hqn : q + 1 ≤ n) (hG0 : 0 ≤ Gb)
    (hxr : xE < 2 ^ (W * n))
    (hxb : ∀ k < n, |ent W ox xE k| ≤ 2 ^ ox)
    (hgb : ∀ s < q * n, |ent W (W - 1) GE s| ≤ Gb)
    (hbound : (n : ℤ) * (2 ^ ox * Gb) < 2 ^ (W - 1))
    (hcheck : rowBlockCheck W ox n q xE GE zE = true) (j : ℕ) (hj : j < q) :
    ∑ k ∈ Finset.range n, ent W ox xE (n - 1 - k) * ent W (W - 1) GE (j * n + k) =
      ent W (W - 1) zE j := by
  simp only [rowBlockCheck, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hcheck
  obtain ⟨⟨hGr, hzr⟩, hM⟩ := hcheck
  have hW1 : 1 ≤ W := by omega
  have hn : 1 ≤ n := by omega
  have hq : 1 ≤ q := by omega
  have hqn' : 1 ≤ q * n := Nat.mul_pos hq hn
  have hjn : j * n + n ≤ q * n := by
    calc j * n + n = (j + 1) * n := by ring
      _ ≤ q * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
  have hVx : ((xE : ℤ) - (offset W ox n : ℤ)) = (dpoly n (ent W ox xE)).eval (2 ^ W) := by
    rw [dpoly_eval, ent_expansion W ox n xE hW1 hxr]
    apply Finset.sum_congr rfl
    intro k _
    rw [← pow_mul]
  have hVG : ((GE : ℤ) - (offset W (W - 1) (q * n) : ℤ)) =
      (dpoly (q * n) (ent W (W - 1) GE)).eval (2 ^ W) := by
    rw [dpoly_eval, ent_expansion W (W - 1) (q * n) GE hW1 hGr]
    apply Finset.sum_congr rfl
    intro k _
    rw [← pow_mul]
  have hX0 : (0 : ℤ) ≤ 2 ^ ox := by positivity
  have hmid := dpoly_mul_coeff_middle n (q * n) (ent W ox xE) (ent W (W - 1) GE) j hn hjn
  have hcoef := dpoly_mul_coeff_abs_le n (q * n) (ent W ox xE) (ent W (W - 1) GE)
    (2 ^ ox) Gb hxb hgb hX0 hG0 (j * n + (n - 1))
  rw [hmid] at hcoef
  have hdig := product_digits W n (q * n) (ent W ox xE) (ent W (W - 1) GE) (2 ^ ox) Gb
    hW1 hn hqn' hxb hgb hX0 hG0 hbound (j * n + (n - 1)) (by omega)
  rw [Polynomial.eval_mul, ← hVx, ← hVG, hmid, show n + q * n = (q + 1) * n by ring] at hdig
  have hMd : dig W (((((xE : ℤ) - (offset W ox n : ℤ)) *
      ((GE : ℤ) - (offset W (W - 1) (q * n) : ℤ)) +
        (offset W (W - 1) ((q + 1) * n) : ℤ)).toNat >>> (W * (n - 1))) &&& blockMask W n q)
        (j * n) =
      dig W ((zE * repunit (W * (n - 1)) q) &&& blockMask W n q) (j * n) :=
    congrArg (fun x => dig W x (j * n)) hM
  rw [dig_land_of_full _ _ _ _ (blockMask_dig W n q j hW1 hn hj),
    dig_land_of_full _ _ _ _ (blockMask_dig W n q j hW1 hn hj), dig_shift, hdig,
    spread_dig W n q zE j hW1 hqn hzr hj] at hMd
  have hnn : 0 ≤ (∑ k ∈ Finset.range n, ent W ox xE (n - 1 - k) * ent W (W - 1) GE (j * n + k)) +
      2 ^ (W - 1) := by
    have := (abs_le.mp hcoef).1
    linarith
  have hfinal : (∑ k ∈ Finset.range n, ent W ox xE (n - 1 - k) * ent W (W - 1) GE (j * n + k)) +
      2 ^ (W - 1) = (dig W zE j : ℤ) := by
    rw [← hMd, Int.toNat_of_nonneg hnn]
  show _ = (dig W zE j : ℤ) - 2 ^ (W - 1)
  linarith

/-! ### Bounds of small operands -/

theorem lt_of_and_high (d W a : ℕ) (haW : a ≤ W) (hd : d < 2 ^ W)
    (h : d &&& ((2 ^ (W - a) - 1) <<< a) = 0) : d < 2 ^ a := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases hiW : i < W
  · have h1 := congrArg (fun x => Nat.testBit x i) h
    have hia : i - a < W - a := by omega
    simp [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, hia] at h1
    simpa using h1
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem highMask_dig (W a L k : ℕ) (hW : 1 ≤ W) (ha : a ≤ W) (hk : k < L) :
    dig W (highMask W a L) k = (2 ^ (W - a) - 1) <<< a := by
  have hB : 0 < 2 ^ W := by positivity
  have hN : (2 ^ (W - a) - 1) <<< a < 2 ^ W := by
    rw [Nat.shiftLeft_eq]
    have h1 : 1 ≤ 2 ^ (W - a) := Nat.one_le_two_pow
    calc (2 ^ (W - a) - 1) * 2 ^ a < 2 ^ (W - a) * 2 ^ a :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = 2 ^ W := by
          rw [← pow_add]
          congr 1
          omega
  have h := repeat_digit (2 ^ W) 1 L ((2 ^ (W - a) - 1) <<< a) k hB le_rfl (by rwa [pow_one]) hk
  rw [Nat.mod_eq_of_lt hN] at h
  simp only [pow_one, mul_one] at h
  have hs : ∑ s ∈ Finset.range L, 2 ^ (W * s) = ∑ s ∈ Finset.range L, (2 ^ W) ^ s :=
    Finset.sum_congr rfl (fun s _ => pow_mul 2 W s)
  unfold highMask dig
  rw [repunit_eq W L hW, hs, pow_mul]
  exact h

theorem boundCheck_sound (W o L E : ℕ) (hW : 1 ≤ W) (ho : o + 1 ≤ W)
    (h : boundCheck W o L E = true) :
    E < 2 ^ (W * L) ∧ ∀ k < L, |ent W o E k| ≤ 2 ^ o := by
  simp only [boundCheck, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hr, hz⟩ := h
  refine ⟨hr, fun k hk => ?_⟩
  have hd0 : dig W (E &&& highMask W (o + 1) L) k = 0 := by
    rw [hz]
    simp [dig]
  rw [dig_land, highMask_dig W (o + 1) L k hW ho hk] at hd0
  have hdW : dig W E k < 2 ^ W := Nat.mod_lt _ (by positivity)
  have hlt : dig W E k < 2 ^ (o + 1) := lt_of_and_high (dig W E k) W (o + 1) ho hdW hd0
  unfold ent
  rw [abs_le]
  have hpos : (0 : ℤ) < 2 ^ o := by positivity
  have hd0' : (0 : ℤ) ≤ (dig W E k : ℤ) := by positivity
  have hlt' : (dig W E k : ℤ) < 2 ^ (o + 1) := by exact_mod_cast hlt
  rw [pow_succ] at hlt'
  constructor
  · linarith
  · linarith

/-! ### Concatenated fibers -/

theorem dig_add_mul_shift (W f C K k : ℕ) (hf : f < 2 ^ (W * K)) :
    dig W (f + C * 2 ^ (W * K)) (K + k) = dig W C k := by
  unfold dig
  rw [show W * (K + k) = W * K + W * k by ring, pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hf, zero_add]

theorem dig_add_mul_high (W f C K k : ℕ) (hk : k < K) :
    dig W (f + C * 2 ^ (W * K)) k = dig W f k := by
  unfold dig
  have hK : W * K = W * k + W + W * (K - k - 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, K = k + 1 + r := ⟨K - (k + 1), by omega⟩
    rw [show k + 1 + r - k - 1 = r by omega]
    ring
  rw [hK, pow_add, pow_add, show f + C * (2 ^ (W * k) * 2 ^ W * 2 ^ (W * (K - k - 1))) =
      f + 2 ^ (W * k) * (2 ^ W * (C * 2 ^ (W * (K - k - 1)))) by ring,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem concatFibers_lt (W L : ℕ) : ∀ (fs : List ℕ), (∀ f ∈ fs, f < 2 ^ (W * L)) →
    concatFibers W L fs < 2 ^ (W * L * fs.length)
  | [], _ => by simp [concatFibers]
  | f :: fs, hf => by
    have hf0 : f < 2 ^ (W * L) := hf f (by simp)
    have ih := concatFibers_lt W L fs (fun g hg => hf g (by simp [hg]))
    simp only [concatFibers, Nat.shiftLeft_eq, List.length_cons]
    rw [show W * L * (fs.length + 1) = W * L + W * L * fs.length by ring, pow_add]
    calc f + concatFibers W L fs * 2 ^ (W * L)
        < 2 ^ (W * L) + concatFibers W L fs * 2 ^ (W * L) := Nat.add_lt_add_right hf0 _
      _ = (concatFibers W L fs + 1) * 2 ^ (W * L) := by ring
      _ ≤ 2 ^ (W * L * fs.length) * 2 ^ (W * L) := Nat.mul_le_mul_right _ ih
      _ = 2 ^ (W * L) * 2 ^ (W * L * fs.length) := mul_comm _ _

theorem concatFibers_dig (W L : ℕ) : ∀ (fs : List ℕ), (∀ f ∈ fs, f < 2 ^ (W * L)) →
    ∀ j k, j < fs.length → k < L →
      dig W (concatFibers W L fs) (j * L + k) = dig W (fs.getD j 0) k
  | [], _, j, k, hj, _ => by simp at hj
  | f :: fs, hf, j, k, hj, hk => by
    have hf0 : f < 2 ^ (W * L) := hf f (by simp)
    simp only [concatFibers, Nat.shiftLeft_eq]
    cases j with
    | zero =>
      simp only [zero_mul, zero_add, List.getD_cons_zero]
      exact dig_add_mul_high W f _ L k hk
    | succ j =>
      simp only [List.getD_cons_succ]
      rw [show (j + 1) * L + k = L + (j * L + k) by ring, dig_add_mul_shift W f _ L _ hf0]
      exact concatFibers_dig W L fs (fun g hg => hf g (by simp [hg])) j k
        (by simpa using hj) hk

/-! ### Many rows against one block operand -/

theorem rowBlockCheckAll_sound (W ox n q GE : ℕ) (Gb : ℤ) (hW : 2 ≤ W) (hqn : q + 1 ≤ n)
    (hG0 : 0 ≤ Gb) (hgb : ∀ s < q * n, |ent W (W - 1) GE s| ≤ Gb)
    (hbound : (n : ℤ) * (2 ^ ox * Gb) < 2 ^ (W - 1)) :
    ∀ (rows : List (ℕ × ℕ)), rowBlockCheckAll W ox n q GE rows = true →
      ∀ p ∈ rows, p.1 < 2 ^ (W * n) → (∀ k < n, |ent W ox p.1 k| ≤ 2 ^ ox) →
        ∀ j < q, ∑ k ∈ Finset.range n, ent W ox p.1 (n - 1 - k) * ent W (W - 1) GE (j * n + k) =
          ent W (W - 1) p.2 j
  | [], _, p, hp, _, _, _, _ => by simp at hp
  | r :: rest, h, p, hp, hxr, hxb, j, hj => by
    simp only [rowBlockCheckAll, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with hpr | hpr
    · rw [hpr] at hxr hxb ⊢
      exact rowBlockCheck_sound W ox n q r.1 GE r.2 Gb hW hqn hG0 hxr hxb hgb hbound h.1 j hj
    · exact rowBlockCheckAll_sound W ox n q GE Gb hW hqn hG0 hgb hbound rest h.2 p hpr hxr hxb j hj

end X2
end ThreeCopyQutritWerner
