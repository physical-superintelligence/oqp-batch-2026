module

public import ThreeCopyQutritWerner.CertificateX2PackedNatAxpy

@[expose] public section


/-!
# Input stage: digit lemmas for concatenation, shifts and periodic masks

Packed naturals hold signed entries in `W`-bit slots (`ent W o E k = dig W E k - 2^o`). This module
proves the digit identities the input stage needs: digits of a concatenation `X + Y·2^(W s)`, of a
left shift, of the low mask `2^(W B) - 1`, of the periodic site masks `siteMask` (slots whose site
index `(k / B) % m` equals `y`), of a masked and shifted natural `siteSel`, and the soundness of the
divide-and-conquer re-packing `spreadDC` (slots of width `wi` moved to width `wo`). It also gives the
reindexing of a sum over `range (A * M)` as a double sum.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

theorem dig_lt (W E k : ℕ) : dig W E k < 2 ^ W := Nat.mod_lt _ (Nat.two_pow_pos W)

theorem dig_zero_of_lt (W E k : ℕ) (h : E < 2 ^ (W * k)) : dig W E k = 0 := by
  unfold dig
  rw [Nat.div_eq_of_lt h, Nat.zero_mod]

theorem dig_zero_nat (W k : ℕ) : dig W 0 k = 0 := by
  unfold dig
  simp

/-- Digits of a concatenation. -/
theorem dig_concat (W s X Y k : ℕ) (hX : X < 2 ^ (W * s)) :
    dig W (X + Y * 2 ^ (W * s)) k = if k < s then dig W X k else dig W Y (k - s) := by
  unfold dig
  split_ifs with hk
  · obtain ⟨d, rfl⟩ : ∃ d, s = k + 1 + d := ⟨s - k - 1, by omega⟩
    have e1 : Y * 2 ^ (W * (k + 1 + d)) = (Y * 2 ^ (W * d) * 2 ^ W) * 2 ^ (W * k) := by
      rw [show W * (k + 1 + d) = W * d + W + W * k by ring, pow_add, pow_add]
      ring
    rw [e1, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]
  · have e1 : 2 ^ (W * k) = 2 ^ (W * s) * 2 ^ (W * (k - s)) := by
      rw [← pow_add]
      congr 1
      rw [← Nat.mul_add]
      congr 1
      omega
    rw [e1, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hX, zero_add]

/-- Digits of a left shift by whole slots. -/
theorem dig_mulPow (W s X k : ℕ) : dig W (X * 2 ^ (W * s)) k = if k < s then 0 else dig W X (k - s) := by
  have h := dig_concat W s 0 X k (Nat.two_pow_pos _)
  rw [zero_add] at h
  rw [h]
  split_ifs
  · exact dig_zero_nat W k
  · rfl

/-- Digits of the low mask of `B` full slots. -/
theorem dig_lowMask (W B t : ℕ) (hW : 1 ≤ W) :
    dig W (2 ^ (W * B) - 1) t = if t < B then 2 ^ W - 1 else 0 := by
  induction B generalizing t with
  | zero =>
    simp only [mul_zero, pow_zero, Nat.sub_self, Nat.not_lt_zero, if_false]
    exact dig_zero_nat W t
  | succ B ih =>
    have h1 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (W * B) := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ (W * B) * 2 ^ W := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlt : 2 ^ W - 1 < 2 ^ (W * 1) := by
      rw [mul_one]
      exact Nat.sub_lt (Nat.two_pow_pos W) one_pos
    have e : 2 ^ (W * (B + 1)) - 1 = (2 ^ W - 1) + (2 ^ (W * B) - 1) * 2 ^ (W * 1) := by
      rw [mul_one, show W * (B + 1) = W * B + W by ring, pow_add]
      zify [h1, h2, h3]
      ring
    rw [e, dig_concat W 1 _ _ t hlt]
    rcases Nat.lt_or_ge t 1 with ht | ht
    · have ht0 : t = 0 := by omega
      subst ht0
      rw [if_pos one_pos, if_pos (Nat.succ_pos B)]
      unfold dig
      rw [mul_zero, pow_zero, Nat.div_one, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos W) one_pos)]
    · have hn1 : ¬ t < 1 := by omega
      rw [if_neg hn1, ih (t - 1)]
      by_cases hb : t - 1 < B
      · have hb' : t < B + 1 := by omega
        rw [if_pos hb, if_pos hb']
      · have hb' : ¬ t < B + 1 := by omega
        rw [if_neg hb, if_neg hb']

/-- The repunit of `A + 1` slots. -/
theorem repunit_succ (W A : ℕ) (hW : 1 ≤ W) : repunit W (A + 1) = repunit W A + 2 ^ (W * A) := by
  rw [repunit_eq W (A + 1) hW, repunit_eq W A hW, Finset.sum_range_succ]

theorem repunit_geom (W A : ℕ) (hW : 1 ≤ W) : repunit W A = ∑ l ∈ Finset.range A, (2 ^ W) ^ l := by
  rw [repunit_eq W A hW]
  apply Finset.sum_congr rfl
  intro l _
  rw [← pow_mul]

/-- Digits of a block repeated with period `p` slots. -/
theorem dig_repeat (W p A blk k : ℕ) (hW : 1 ≤ W) (hp : 1 ≤ p) (hblk : blk < 2 ^ (W * p)) :
    dig W (blk * repunit (W * p) A) k = if k < A * p then dig W blk (k % p) else 0 := by
  have hWp : 1 ≤ W * p := Nat.mul_pos (by omega) (by omega)
  induction A with
  | zero =>
    simp only [zero_mul, Nat.not_lt_zero, if_false]
    rw [repunit_eq _ 0 hWp, Finset.sum_range_zero, mul_zero]
    exact dig_zero_nat W k
  | succ A ih =>
    have hX : blk * repunit (W * p) A < 2 ^ (W * (A * p)) := by
      rw [repunit_geom (W * p) A hWp, show W * (A * p) = (W * p) * A by ring, pow_mul 2 (W * p) A]
      exact geom_lt (2 ^ (W * p)) blk hblk A
    rw [repunit_succ (W * p) A hWp, mul_add, show W * p * A = W * (A * p) by ring,
      dig_concat W (A * p) _ _ k hX, ih]
    have hq : (A + 1) * p = A * p + p := by ring
    rw [hq]
    by_cases h1 : k < A * p
    · have h1' : k < A * p + p := lt_of_lt_of_le h1 (Nat.le_add_right _ _)
      rw [if_pos h1, if_pos h1, if_pos h1']
    · rw [if_neg h1]
      have hle : A * p ≤ k := Nat.le_of_not_lt h1
      by_cases h2 : k < A * p + p
      · rw [if_pos h2]
        congr 1
        have hr : k - A * p < p := by omega
        have hk : k = p * A + (k - A * p) := by
          rw [Nat.mul_comm p A, Nat.add_sub_cancel' hle]
        conv_rhs => rw [hk]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      · rw [if_neg h2]
        apply dig_zero_of_lt
        have hr : p ≤ k - A * p := by omega
        calc blk < 2 ^ (W * p) := hblk
          _ ≤ 2 ^ (W * (k - A * p)) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left W hr)

/-- The selection mask of the slots whose site index `(k / B) % m` is `y` (`A` periods of `m * B`
slots). -/
def siteMask (W A m B y : ℕ) : ℕ := (2 ^ (W * B) - 1) * 2 ^ (W * (B * y)) * repunit (W * (m * B)) A

theorem siteBlk_dig (W B y t : ℕ) (hW : 1 ≤ W) :
    dig W ((2 ^ (W * B) - 1) * 2 ^ (W * (B * y))) t =
      if B * y ≤ t ∧ t < B * y + B then 2 ^ W - 1 else 0 := by
  rw [dig_mulPow]
  by_cases h : t < B * y
  · have h' : ¬ (B * y ≤ t ∧ t < B * y + B) := fun h'' => absurd h''.1 (Nat.not_le_of_lt h)
    rw [if_pos h, if_neg h']
  · rw [if_neg h, dig_lowMask W B _ hW]
    by_cases h2 : t - B * y < B
    · have h3 : B * y ≤ t ∧ t < B * y + B := ⟨Nat.le_of_not_lt h, by omega⟩
      rw [if_pos h2, if_pos h3]
    · have h3 : ¬ (B * y ≤ t ∧ t < B * y + B) := fun h'' => h2 (by omega)
      rw [if_neg h2, if_neg h3]

theorem siteBlk_lt (W m B y : ℕ) (hy : y < m) :
    (2 ^ (W * B) - 1) * 2 ^ (W * (B * y)) < 2 ^ (W * (m * B)) := by
  have h1 : (2 ^ (W * B) - 1) * 2 ^ (W * (B * y)) < 2 ^ (W * B) * 2 ^ (W * (B * y)) :=
    Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) one_pos) (Nat.two_pow_pos _)
  calc (2 ^ (W * B) - 1) * 2 ^ (W * (B * y)) < 2 ^ (W * B) * 2 ^ (W * (B * y)) := h1
    _ = 2 ^ (W * (B * (y + 1))) := by rw [← pow_add]; congr 1; ring
    _ ≤ 2 ^ (W * (m * B)) := Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left W (by rw [Nat.mul_comm m B]; exact Nat.mul_le_mul_left B hy))

theorem site_div_eq (B y r : ℕ) (hB : 1 ≤ B) : (B * y ≤ r ∧ r < B * y + B) ↔ r / B = y := by
  have hB0 : 0 < B := by omega
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : r / B < y + 1 := (Nat.div_lt_iff_lt_mul hB0).mpr (by
      rw [Nat.add_mul, one_mul, Nat.mul_comm y B]
      exact h2)
    have h4 : y ≤ r / B := (Nat.le_div_iff_mul_le hB0).mpr (by rw [Nat.mul_comm]; exact h1)
    omega
  · intro h
    subst h
    constructor
    · exact Nat.mul_div_le r B
    · have h5 := Nat.lt_mul_div_succ r hB0
      rw [Nat.mul_add, Nat.mul_one] at h5
      exact h5

theorem siteMask_dig (W A m B y k : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (hy : y < m) :
    dig W (siteMask W A m B y) k = if k < A * (m * B) ∧ k / B % m = y then 2 ^ W - 1 else 0 := by
  have hp : 1 ≤ m * B := Nat.mul_pos (by omega) (by omega)
  unfold siteMask
  rw [dig_repeat W (m * B) A _ k hW hp (siteBlk_lt W m B y hy)]
  by_cases hk : k < A * (m * B)
  · rw [if_pos hk, siteBlk_dig W B y _ hW]
    have e : k % (m * B) / B = k / B % m := by
      rw [Nat.mul_comm m B]
      exact Nat.mod_mul_right_div_self k B m
    by_cases h : B * y ≤ k % (m * B) ∧ k % (m * B) < B * y + B
    · have hs : k / B % m = y := by rw [← e]; exact (site_div_eq B y _ hB).mp h
      rw [if_pos h, if_pos (And.intro hk hs)]
    · have hs : ¬ (k < A * (m * B) ∧ k / B % m = y) := fun h' =>
        h ((site_div_eq B y _ hB).mpr (by rw [e]; exact h'.2))
      rw [if_neg h, if_neg hs]
  · have hs : ¬ (k < A * (m * B) ∧ k / B % m = y) := fun h => hk h.1
    rw [if_neg hk, if_neg hs]

/-- The slots of site index `y`, moved down by `B * y` slots. -/
def siteSel (W A m B y E : ℕ) : ℕ := (E &&& siteMask W A m B y) >>> (W * (B * y))

theorem siteSel_dig (W A m B y E k : ℕ) (hW : 1 ≤ W) (hB : 1 ≤ B) (hy : y < m) :
    dig W (siteSel W A m B y E) k =
      if k + B * y < A * (m * B) ∧ (k + B * y) / B % m = y then dig W E (k + B * y) else 0 := by
  unfold siteSel
  rw [dig_shift, dig_land, siteMask_dig W A m B y (k + B * y) hW hB hy]
  split_ifs
  · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (dig_lt W E _)]
  · exact Nat.and_zero _

/-! ### Sums over a product range -/

theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (A P : ℕ) :
    ∑ k ∈ Finset.range (A * P), f k = ∑ a ∈ Finset.range A, ∑ j ∈ Finset.range P, f (a * P + j) := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [show (A + 1) * P = A * P + P by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A sum over the slots `k < A * (m * B)` as a triple sum over `(a, t, b)`, `k = (a m + t) B + b`. -/
theorem sum_range_site {M : Type*} [AddCommMonoid M] (f : ℕ → M) (A m B : ℕ) :
    ∑ k ∈ Finset.range (A * (m * B)), f k =
      ∑ a ∈ Finset.range A, ∑ t ∈ Finset.range m, ∑ b ∈ Finset.range B, f ((a * m + t) * B + b) := by
  rw [sum_range_mul_split f A (m * B)]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_range_mul_split (fun j => f (a * (m * B) + j)) m B]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ring

/-! ### Divide-and-conquer re-packing of slots -/

/-- The low `n` slots (width `wi`) of `P`, re-packed at width `wo` (one slot per step). -/
noncomputable def spreadLeaf (wi wo : ℕ) (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih P => (P &&& (2 ^ wi - 1)) + (ih (P >>> wi) <<< wo)) n

/-- Divide-and-conquer re-packing of the low `n` slots of width `wi` at width `wo` (`k` levels). -/
noncomputable def spreadDC (wi wo : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun n P => spreadLeaf wi wo n P)
    (fun _ ih n P => if n ≤ 8 then spreadLeaf wi wo n P else
      ih (n / 2) (P &&& (2 ^ (wi * (n / 2)) - 1)) +
        (ih (n - n / 2) (P >>> (wi * (n / 2))) <<< (wo * (n / 2)))) k

theorem spreadLeaf_eq (wi wo : ℕ) : ∀ (n P : ℕ),
    spreadLeaf wi wo n P = ∑ t ∈ Finset.range n, dig wi P t * 2 ^ (wo * t)
  | 0, P => by simp [spreadLeaf]
  | n + 1, P => by
    show (P &&& (2 ^ wi - 1)) + (spreadLeaf wi wo n (P >>> wi) <<< wo) = _
    rw [spreadLeaf_eq wi wo n (P >>> wi), Finset.sum_range_succ', Nat.shiftLeft_eq,
      Nat.and_two_pow_sub_one_eq_mod, Finset.sum_mul, add_comm (P % 2 ^ wi)]
    congr 1
    · apply Finset.sum_congr rfl
      intro t _
      have h := dig_shift wi P 1 t
      rw [mul_one] at h
      rw [h, mul_assoc, ← pow_add]
      congr 2
      all_goals ring
    · unfold dig
      simp

theorem spreadDC_eq (wi wo : ℕ) : ∀ (k n P : ℕ),
    spreadDC wi wo k n P = ∑ t ∈ Finset.range n, dig wi P t * 2 ^ (wo * t)
  | 0, n, P => spreadLeaf_eq wi wo n P
  | k + 1, n, P => by
    show (if n ≤ 8 then spreadLeaf wi wo n P else
      spreadDC wi wo k (n / 2) (P &&& (2 ^ (wi * (n / 2)) - 1)) +
        (spreadDC wi wo k (n - n / 2) (P >>> (wi * (n / 2))) <<< (wo * (n / 2)))) = _
    split_ifs with hn
    · exact spreadLeaf_eq wi wo n P
    · rw [spreadDC_eq wi wo k, spreadDC_eq wi wo k, Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod,
        Finset.sum_mul]
      have hsplit : n = n / 2 + (n - n / 2) := by omega
      conv_rhs => rw [hsplit, Finset.sum_range_add]
      have hP : P = P % 2 ^ (wi * (n / 2)) + (P >>> (wi * (n / 2))) * 2 ^ (wi * (n / 2)) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.mod_add_div']
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        have ht' := Finset.mem_range.mp ht
        congr 1
        conv_rhs => rw [hP]
        rw [dig_concat wi (n / 2) _ _ t (Nat.mod_lt _ (Nat.two_pow_pos _)), if_pos ht']
      · apply Finset.sum_congr rfl
        intro t _
        have h := dig_shift wi P (n / 2) t
        rw [h, mul_assoc, ← pow_add, Nat.add_comm t (n / 2)]
        congr 2
        all_goals ring

/-- Digit `t < n` of a re-packed natural, for `wi ≤ wo`. -/
theorem spreadDC_dig (wi wo k n P t : ℕ) (hw : wi ≤ wo) (ht : t < n) :
    dig wo (spreadDC wi wo k n P) t = dig wi P t := by
  rw [spreadDC_eq]
  unfold dig
  have h := sum_digit (2 ^ wo) n (fun s => P / 2 ^ (wi * s) % 2 ^ wi) (Nat.two_pow_pos wo)
    (fun s => lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos wi)) (Nat.pow_le_pow_right (by norm_num) hw)) t ht
  simp only [← pow_mul] at h
  exact h

end X2
end ThreeCopyQutritWerner
