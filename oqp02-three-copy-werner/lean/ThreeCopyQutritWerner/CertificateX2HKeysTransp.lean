module

public import ThreeCopyQutritWerner.CertificateX2InputSite
public import ThreeCopyQutritWerner.CertificateX2HKeysCarrierRed
public import ThreeCopyQutritWerner.CertificateX2PackedGlue

@[expose] public section


/-!
# The three transposition identities of an h image, as packed kernel checks

An image column `P` (11-bit slots, offset `2^10`) is re-packed at `W` bits and contracted site by
site with the integer action of a transposition (`tApply`, built from `siteApply` of CertificateX2InputSite). `colCheck` checks,
for one column, `ρ((1 2)) P = -P`, `ρ((3 4)) P = -P` and `∑_t ρ(t) P = 2 P` (the last as one natural
linear combination, `natAxpyCheck`). The generic lemmas `hsSiteVal_abs_le`, `hsEnt_abs_le`,
`hsSite_decomp`, `hsSiteApply_bound`, `hsSpreadW`, `hsSpreadW_spec` are the lemmas of CertificateX2InputV, renamed. `colCheck_sound` gives the identities slot by
slot as triple sums.
-/

set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-! ## Generic lemmas (renamed copies from CertificateX2InputV) -/

theorem hsSiteVal_abs_le (W m B : ℕ) (gp gn : ℕ → ℕ → ℕ) (E a x b : ℕ) (M R : ℤ) (hM : 0 ≤ M)
    (hE : ∀ y < m, |ent W (W - 1) E ((a * m + y) * B + b)| ≤ M)
    (hR : ∑ y ∈ Finset.range m, ((gp x y : ℤ) + gn x y) ≤ R) :
    |siteVal W m B gp gn E a x b| ≤ R * M := by
  unfold siteVal
  calc |∑ y ∈ Finset.range m, ((gp x y : ℤ) - gn x y) * ent W (W - 1) E ((a * m + y) * B + b)|
      ≤ ∑ y ∈ Finset.range m, |((gp x y : ℤ) - gn x y) * ent W (W - 1) E ((a * m + y) * B + b)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ Finset.range m, ((gp x y : ℤ) + gn x y) * M := by
        apply Finset.sum_le_sum
        intro y hy
        rw [abs_mul]
        have h1 : |((gp x y : ℤ) - gn x y)| ≤ (gp x y : ℤ) + gn x y := by
          calc |((gp x y : ℤ) - gn x y)| = |(gp x y : ℤ) + -(gn x y : ℤ)| := by rw [sub_eq_add_neg]
            _ ≤ |(gp x y : ℤ)| + |-(gn x y : ℤ)| := abs_add_le _ _
            _ = (gp x y : ℤ) + gn x y := by rw [abs_neg, abs_of_nonneg (by positivity),
                abs_of_nonneg (by positivity)]
        exact mul_le_mul h1 (hE y (Finset.mem_range.mp hy)) (abs_nonneg _) (by positivity)
    _ = (∑ y ∈ Finset.range m, ((gp x y : ℤ) + gn x y)) * M := by rw [Finset.sum_mul]
    _ ≤ R * M := mul_le_mul_of_nonneg_right hR hM

theorem hsEnt_abs_le (W E k : ℕ) (hW : 1 ≤ W) : |ent W (W - 1) E k| ≤ 2 ^ (W - 1) := by
  have h := ent_range W E k hW
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem hsSite_decomp (m B k : ℕ) (hm : 1 ≤ m) (hB : 1 ≤ B) :
    k = (k / (m * B) * m + k / B % m) * B + k % B := by
  have e1 : k / (m * B) = k / B / m := by rw [Nat.mul_comm m B, Nat.div_div_eq_div_mul]
  have e2 := Nat.div_add_mod (k / B) m
  have e3 := Nat.div_add_mod k B
  rw [e1]
  calc k = B * (k / B) + k % B := e3.symm
    _ = B * (m * (k / B / m) + k / B % m) + k % B := by rw [e2]
    _ = (k / B / m * m + k / B % m) * B + k % B := by ring

theorem hsSiteApply_bound (W A m B : ℕ) (gp gn : ℕ → ℕ → ℕ) (E M R : ℕ) (hW : 2 ≤ W) (hB : 1 ≤ B)
    (hm : 1 ≤ m) (hE : E < 2 ^ (W * (A * (m * B))))
    (hEb : ∀ k < A * (m * B), |ent W (W - 1) E k| ≤ M)
    (hR : ∀ x < m, ∑ y ∈ Finset.range m, ((gp x y : ℤ) + gn x y) ≤ R)
    (hRM : R * M < 2 ^ (W - 1)) :
    siteApply W A m B gp gn E < 2 ^ (W * (A * (m * B))) ∧
      (∀ k < A * (m * B), |ent W (W - 1) (siteApply W A m B gp gn E) k| ≤ ((R * M : ℕ) : ℤ)) ∧
      ∀ a < A, ∀ x < m, ∀ b < B,
        ent W (W - 1) (siteApply W A m B gp gn E) ((a * m + x) * B + b) = siteVal W m B gp gn E a x b := by
  have hRM' : ((R : ℤ) * (M : ℤ)) < 2 ^ (W - 1) := by exact_mod_cast hRM
  have hval : ∀ a < A, ∀ x < m, ∀ b < B, |siteVal W m B gp gn E a x b| ≤ (R : ℤ) * M := by
    intro a ha x hx b hb
    exact hsSiteVal_abs_le W m B gp gn E a x b M R (by positivity)
      (fun y hy => hEb _ (site_idx_lt A m B a y b ha hy hb)) (hR x hx)
  have hv : ∀ a < A, ∀ x < m, ∀ b < B, -(2 ^ (W - 1) : ℤ) ≤ siteVal W m B gp gn E a x b ∧
      siteVal W m B gp gn E a x b < 2 ^ (W - 1) := by
    intro a ha x hx b hb
    have h := abs_le.mp (hval a ha x hx b hb)
    constructor <;> linarith [h.1, h.2]
  obtain ⟨hlt, hent⟩ := siteApply_spec W A m B gp gn E hW hB hm hE hv
  refine ⟨hlt, ?_, hent⟩
  intro k hk
  have hmB : 0 < m * B := Nat.mul_pos (by omega) (by omega)
  have ha : k / (m * B) < A := (Nat.div_lt_iff_lt_mul hmB).mpr hk
  have hx : k / B % m < m := Nat.mod_lt _ (by omega)
  have hb : k % B < B := Nat.mod_lt _ (by omega)
  rw [hsSite_decomp m B k hm hB, hent _ ha _ hx _ hb]
  push_cast
  exact hval _ ha _ hx _ hb

/-- Re-packing of an 11-bit image column at `W` bits with offset `2^(W-1)`. -/
def hsSpreadW (W n P : ℕ) : ℕ := spreadDC 11 W 16 n P + (2 ^ (W - 1) - 2 ^ 10) * repunit W n

theorem hsSpreadW_sum (W n P : ℕ) (hW : 12 ≤ W) :
    hsSpreadW W n P = ∑ t ∈ Finset.range n, (dig 11 P t + (2 ^ (W - 1) - 2 ^ 10)) * (2 ^ W) ^ t := by
  have hW1 : 1 ≤ W := by omega
  unfold hsSpreadW
  rw [spreadDC_eq, repunit_eq W n hW1, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← pow_mul]
  ring

theorem hsSpreadW_spec (W n P : ℕ) (hW : 12 ≤ W) :
    hsSpreadW W n P < 2 ^ (W * n) ∧ ∀ t < n, ent W (W - 1) (hsSpreadW W n P) t = ent 11 10 P t := by
  have hoff : 2 ^ 10 ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcoef : ∀ t, dig 11 P t + (2 ^ (W - 1) - 2 ^ 10) < 2 ^ W := by
    intro t
    have h1 := dig_lt 11 P t
    have h2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : (2 : ℕ) ^ 11 = 2 * 2 ^ 10 := by norm_num
    omega
  have hsum := hsSpreadW_sum W n P hW
  constructor
  · rw [hsum, pow_mul]
    exact sum_digits_lt (2 ^ W) _ hcoef n
  · intro t ht
    have hd : dig W (hsSpreadW W n P) t = dig 11 P t + (2 ^ (W - 1) - 2 ^ 10) := by
      rw [hsum]
      unfold dig
      rw [pow_mul 2 W t]
      exact sum_digit (2 ^ W) n _ (Nat.two_pow_pos W) hcoef t ht
    unfold ent
    rw [hd, Nat.cast_add, Nat.cast_sub hoff]
    push_cast
    ring

/-! ## Negated and doubled re-packed columns -/

theorem hsOffset_sum (W n : ℕ) (hW : 1 ≤ W) :
    offset W (W - 1) n = ∑ t ∈ Finset.range n, 2 ^ (W - 1) * (2 ^ W) ^ t := by
  unfold offset
  rw [repunit_eq W n hW, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [← pow_mul]

/-- Digit of the negated re-packed column. -/
def negDig (W d : ℕ) : ℕ := 2 ^ (W - 1) + 2 ^ 10 - d

/-- Digit of the doubled re-packed column. -/
def dblDig (W d : ℕ) : ℕ := 2 * d + 2 ^ (W - 1) - 2 ^ 11

theorem negSpread_eq (W n P : ℕ) (hW : 12 ≤ W) :
    2 * offset W (W - 1) n - hsSpreadW W n P = ∑ t ∈ Finset.range n, negDig W (dig 11 P t) * (2 ^ W) ^ t := by
  have h10l : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have h11l : (2 : ℕ) ^ 11 = 2048 := by norm_num
  have h12l : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hW1 : 1 ≤ W := by omega
  have hoff : 2 ^ 10 ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : ∀ t ∈ Finset.range n, (dig 11 P t + (2 ^ (W - 1) - 2 ^ 10)) * (2 ^ W) ^ t ≤
      2 * (2 ^ (W - 1) * (2 ^ W) ^ t) := by
    intro t _
    have := dig_lt 11 P t
    rw [← Nat.mul_assoc]
    apply Nat.mul_le_mul_right
    have h11 : (2 : ℕ) ^ 11 = 2 * 2 ^ 10 := by norm_num
    omega
  rw [hsOffset_sum W n hW1, hsSpreadW_sum W n P hW, Finset.mul_sum, ← Finset.sum_tsub_distrib _ hle]
  apply Finset.sum_congr rfl
  intro t _
  have hd := dig_lt 11 P t
  have h11 : (2 : ℕ) ^ 11 = 2 * 2 ^ 10 := by norm_num
  unfold negDig
  rw [← Nat.mul_assoc, ← Nat.sub_mul]
  congr 1
  omega

theorem negSpread_ent (W n P : ℕ) (hW : 12 ≤ W) (k : ℕ) (hk : k < n) :
    ent W (W - 1) (2 * offset W (W - 1) n - hsSpreadW W n P) k = -ent 11 10 P k := by
  have h10l : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have h11l : (2 : ℕ) ^ 11 = 2048 := by norm_num
  have h12l : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hoff : 2 ^ 10 < 2 ^ (W - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hB2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hdl : ∀ t, dig 11 P t < 2 ^ 11 := fun t => dig_lt 11 P t
  have h11 : (2 : ℕ) ^ 11 = 2 * 2 ^ 10 := by norm_num
  have hf : ∀ t, negDig W (dig 11 P t) < 2 ^ W := by
    intro t
    have := hdl t
    unfold negDig
    omega
  have hd : dig W (2 * offset W (W - 1) n - hsSpreadW W n P) k = negDig W (dig 11 P k) := by
    rw [negSpread_eq W n P hW]
    unfold dig
    rw [pow_mul 2 W k]
    exact sum_digit (2 ^ W) n (fun t => negDig W (dig 11 P t)) (Nat.two_pow_pos W) hf k hk
  unfold ent
  rw [hd]
  have := hdl k
  unfold negDig
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem dblSpread_eq (W n P : ℕ) (hW : 13 ≤ W) :
    2 * hsSpreadW W n P - offset W (W - 1) n = ∑ t ∈ Finset.range n, dblDig W (dig 11 P t) * (2 ^ W) ^ t := by
  have h10l : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have h11l : (2 : ℕ) ^ 11 = 2048 := by norm_num
  have h12l : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hW1 : 1 ≤ W := by omega
  have hoff : 2 ^ 11 ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h11 : (2 : ℕ) ^ 11 = 2 * 2 ^ 10 := by norm_num
  have hle : ∀ t ∈ Finset.range n, 2 ^ (W - 1) * (2 ^ W) ^ t ≤
      2 * ((dig 11 P t + (2 ^ (W - 1) - 2 ^ 10)) * (2 ^ W) ^ t) := by
    intro t _
    rw [← Nat.mul_assoc]
    apply Nat.mul_le_mul_right
    omega
  rw [hsOffset_sum W n hW1, hsSpreadW_sum W n P (by omega), Finset.mul_sum, ← Finset.sum_tsub_distrib _ hle]
  apply Finset.sum_congr rfl
  intro t _
  have hd := dig_lt 11 P t
  unfold dblDig
  rw [← Nat.mul_assoc, ← Nat.sub_mul]
  congr 1
  omega

theorem dblSpread_ent (W n P : ℕ) (hW : 13 ≤ W) (k : ℕ) (hk : k < n) :
    ent W (W - 1) (2 * hsSpreadW W n P - offset W (W - 1) n) k = 2 * ent 11 10 P k := by
  have h10l : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have h11l : (2 : ℕ) ^ 11 = 2048 := by norm_num
  have h12l : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hoff : 2 ^ 12 ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hdl : ∀ t, dig 11 P t < 2 ^ 11 := fun t => dig_lt 11 P t
  have h11 : (2 : ℕ) ^ 11 = 2 * 2 ^ 10 := by norm_num
  have h12 : (2 : ℕ) ^ 12 = 2 * 2 ^ 11 := by norm_num
  have hf : ∀ t, dblDig W (dig 11 P t) < 2 ^ W := by
    intro t
    have := hdl t
    unfold dblDig
    omega
  have hd : dig W (2 * hsSpreadW W n P - offset W (W - 1) n) k = dblDig W (dig 11 P k) := by
    rw [dblSpread_eq W n P hW]
    unfold dig
    rw [pow_mul 2 W k]
    exact sum_digit (2 ^ W) n (fun t => dblDig W (dig 11 P t)) (Nat.two_pow_pos W) hf k hk
  unfold ent
  rw [hd]
  have := hdl k
  unfold dblDig
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-! ## The transposition actions as site contractions -/

/-- Entry `(x, y)` of an integer matrix, `0` outside. -/
def aEntT {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x y : ℕ) : ℤ :=
  if hx : x < n then if hy : y < n then A ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0

/-- Entry `(x, y)` of the type-`t` action of the carrier permutation `p`. -/
def aEnt (t : Fin 7) (p : Fin 120) : ℕ → ℕ → ℤ :=
  ![aEntT (x2hA0 p), aEntT (x2hA1 p), aEntT (x2hA2 p), aEntT (x2hA3 p), aEntT (x2hA4 p), aEntT (x2hA5 p),
    aEntT (x2hA6 p)] t

def tAp (t : Fin 7) (p : Fin 120) (x y : ℕ) : ℕ := (aEnt t p x y).toNat

def tAn (t : Fin 7) (p : Fin 120) (x y : ℕ) : ℕ := (-aEnt t p x y).toNat

theorem tAp_sub_tAn (t : Fin 7) (p : Fin 120) (x y : ℕ) :
    ((tAp t p x y : ℕ) : ℤ) - (tAn t p x y : ℤ) = aEnt t p x y := Int.toNat_sub_toNat_neg _

/-- Row absolute sums of an action matrix, checked by the kernel against a bound. -/
def tRowOK (t : Fin 7) (p : Fin 120) (m b : ℕ) : Bool :=
  (List.range m).all (fun x => Nat.ble (natSum m (fun y => tAp t p x y + tAn t p x y)) b)

theorem tRowOK_sound (t : Fin 7) (p : Fin 120) (m b : ℕ) (h : tRowOK t p m b = true) (x : ℕ) (hx : x < m) :
    ∑ y ∈ Finset.range m, (((tAp t p x y : ℕ) : ℤ) + (tAn t p x y : ℤ)) ≤ b := by
  unfold tRowOK at h
  have hx' := Nat.le_of_ble_eq_true (List.all_eq_true.mp h x (List.mem_range.mpr hx))
  rw [natSum_eq] at hx'
  have e : ∑ y ∈ Finset.range m, (((tAp t p x y : ℕ) : ℤ) + (tAn t p x y : ℤ)) =
      ((∑ y ∈ Finset.range m, (tAp t p x y + tAn t p x y) : ℕ) : ℤ) := by push_cast; rfl
  rw [e]
  exact_mod_cast hx'

/-- The column `(A_t0 ⊗ A_t1 ⊗ A_t2) P` of one carrier permutation (sites 2, 1, 0). -/
def tApply (W : ℕ) (p : Fin 120) (t0 t1 t2 : Fin 7) (m0 m1 m2 P : ℕ) : ℕ :=
  siteApply W 1 m0 (m1 * m2) (tAp t0 p) (tAn t0 p)
    (siteApply W m0 m1 m2 (tAp t1 p) (tAn t1 p)
      (siteApply W (m0 * m1) m2 1 (tAp t2 p) (tAn t2 p) (hsSpreadW W (m0 * m1 * m2) P)))

theorem tApply_sound (W : ℕ) (p : Fin 120) (t0 t1 t2 : Fin 7) (m0 m1 m2 P : ℕ) (hW : 24 ≤ W)
    (h0 : 1 ≤ m0) (h1 : 1 ≤ m1) (h2 : 1 ≤ m2)
    (hr0 : tRowOK t0 p m0 16 = true) (hr1 : tRowOK t1 p m1 16 = true) (hr2 : tRowOK t2 p m2 16 = true) :
    tApply W p t0 t1 t2 m0 m1 m2 P < 2 ^ (W * (m0 * m1 * m2)) ∧
      (∀ k < m0 * m1 * m2, |ent W (W - 1) (tApply W p t0 t1 t2 m0 m1 m2 P) k| ≤ 2 ^ 22) ∧
      ∀ y0 < m0, ∀ y1 < m1, ∀ y2 < m2,
      ent W (W - 1) (tApply W p t0 t1 t2 m0 m1 m2 P) ((y0 * m1 + y1) * m2 + y2) =
        ∑ z0 ∈ Finset.range m0, ∑ z1 ∈ Finset.range m1, ∑ z2 ∈ Finset.range m2,
          aEnt t0 p y0 z0 * (aEnt t1 p y1 z1 * (aEnt t2 p y2 z2 * ent 11 10 P ((z0 * m1 + z1) * m2 + z2))) := by
  have hW2 : 2 ≤ W := by omega
  have hpw : ∀ e, e ≤ 22 → (2 : ℕ) ^ e < 2 ^ (W - 1) := fun e he =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold tApply
  obtain ⟨hEl, hEe⟩ := hsSpreadW_spec W (m0 * m1 * m2) P (by omega)
  -- stage 2 (B = 1)
  have hL2 : m0 * m1 * (m2 * 1) = m0 * m1 * m2 := by ring
  have hEb2 : ∀ k < m0 * m1 * (m2 * 1), |ent W (W - 1) (hsSpreadW W (m0 * m1 * m2) P) k| ≤ 2 ^ 10 := by
    intro k hk
    rw [hL2] at hk
    rw [hEe k hk]
    have := hsEnt_abs_le 11 P k (by norm_num)
    simpa using this
  obtain ⟨hS2l, hS2b, hS2e⟩ := hsSiteApply_bound W (m0 * m1) m2 1 (tAp t2 p) (tAn t2 p)
    (hsSpreadW W (m0 * m1 * m2) P) (2 ^ 10) 16 hW2 le_rfl h2 (by rw [hL2]; exact hEl) hEb2
    (tRowOK_sound t2 p m2 16 hr2) (by
      calc 16 * 2 ^ 10 = 2 ^ 14 := by norm_num
        _ < 2 ^ (W - 1) := hpw 14 (by norm_num))
  -- stage 1
  have hL1 : m0 * (m1 * m2) = m0 * m1 * (m2 * 1) := by ring
  obtain ⟨hS1l, hS1b, hS1e⟩ := hsSiteApply_bound W m0 m1 m2 (tAp t1 p) (tAn t1 p) _ (16 * 2 ^ 10) 16 hW2 h2 h1
    (by rw [hL1]; exact hS2l) (by intro k hk; rw [hL1] at hk; exact hS2b k hk)
    (tRowOK_sound t1 p m1 16 hr1) (by
      calc 16 * (16 * 2 ^ 10) = 2 ^ 18 := by norm_num
        _ < 2 ^ (W - 1) := hpw 18 (by norm_num))
  -- stage 0
  have hL0 : 1 * (m0 * (m1 * m2)) = m0 * (m1 * m2) := by ring
  obtain ⟨hS0l, hS0b, hS0e⟩ := hsSiteApply_bound W 1 m0 (m1 * m2) (tAp t0 p) (tAn t0 p) _
    (16 * (16 * 2 ^ 10)) 16 hW2 (Nat.mul_pos (by omega) (by omega)) h0
    (by rw [hL0]; exact hS1l) (by intro k hk; rw [hL0] at hk; exact hS1b k hk)
    (tRowOK_sound t0 p m0 16 hr0) (by
      calc 16 * (16 * (16 * 2 ^ 10)) = 2 ^ 22 := by norm_num
        _ < 2 ^ (W - 1) := hpw 22 (by norm_num))
  have hn : m0 * m1 * m2 = 1 * (m0 * (m1 * m2)) := by ring
  refine ⟨lt_of_lt_of_eq hS0l (by rw [hn]), ?_, ?_⟩
  · intro k hk
    rw [hn] at hk
    have h22 := hS0b k hk
    have e22 : ((16 * (16 * (16 * 2 ^ 10)) : ℕ) : ℤ) = 2 ^ 22 := by norm_num
    rw [e22] at h22
    exact h22
  · intro y0 hy0 y1 hy1 y2 hy2
    have i0 : (y0 * m1 + y1) * m2 + y2 = (0 * m0 + y0) * (m1 * m2) + (y1 * m2 + y2) := by ring
    have hb0 : y1 * m2 + y2 < m1 * m2 := by nlinarith
    rw [i0, hS0e 0 (by norm_num) y0 hy0 _ hb0]
    unfold siteVal
    apply Finset.sum_congr rfl
    intro z0 hz0
    have hz0' := Finset.mem_range.mp hz0
    have i1 : (0 * m0 + z0) * (m1 * m2) + (y1 * m2 + y2) = (z0 * m1 + y1) * m2 + y2 := by ring
    rw [i1, hS1e z0 hz0' y1 hy1 y2 hy2, tAp_sub_tAn]
    unfold siteVal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z1 hz1
    have hz1' := Finset.mem_range.mp hz1
    have i2 : (z0 * m1 + z1) * m2 + y2 = ((z0 * m1 + z1) * m2 + y2) * 1 + 0 := by ring
    have ha2 : z0 * m1 + z1 < m0 * m1 := by nlinarith
    rw [i2, hS2e (z0 * m1 + z1) ha2 y2 hy2 0 (by norm_num), tAp_sub_tAn]
    unfold siteVal
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z2 hz2
    have hz2' := Finset.mem_range.mp hz2
    have i3 : ((z0 * m1 + z1) * m2 + z2) * 1 + 0 = (z0 * m1 + z1) * m2 + z2 := by ring
    have hk3 : (z0 * m1 + z1) * m2 + z2 < m0 * m1 * m2 := by
      have := site_idx_lt m0 m1 m2 z0 z1 z2 hz0' hz1' hz2'
      rwa [← Nat.mul_assoc] at this
    rw [i3, hEe _ hk3, tAp_sub_tAn]

/-! ## The per-column check -/

/-- One image column: `ρ((1 2)) P = -P`, `ρ((3 4)) P = -P`, `∑_t ρ(t) P = 2 P` (`W`-bit slots). -/
def colCheck (W : ℕ) (t0 t1 t2 : Fin 7) (m0 m1 m2 P : ℕ) : Bool :=
  Nat.beq (tApply W (x2hSpecial 5) t0 t1 t2 m0 m1 m2 P)
      (2 * offset W (W - 1) (m0 * m1 * m2) - hsSpreadW W (m0 * m1 * m2) P) &&
    Nat.beq (tApply W (x2hSpecial 10) t0 t1 t2 m0 m1 m2 P)
      (2 * offset W (W - 1) (m0 * m1 * m2) - hsSpreadW W (m0 * m1 * m2) P) &&
    natAxpyCheck W (m0 * m1 * m2) 1 (List.ofFn fun _ : Fin 10 => 3)
      (List.ofFn fun u : Fin 10 => tApply W (x2hSpecial u.succ.castSucc) t0 t1 t2 m0 m1 m2 P)
      (2 * hsSpreadW W (m0 * m1 * m2) P - offset W (W - 1) (m0 * m1 * m2))
      (natAxpyCorr W (m0 * m1 * m2) 1
        (List.ofFn fun u : Fin 10 => tApply W (x2hSpecial u.succ.castSucc) t0 t1 t2 m0 m1 m2 P))

/-- The ten transpositions and their row bounds (kernel). -/
theorem x2hTranspRows : ∀ u : Fin 10, ∀ t : Fin 7,
    tRowOK t (x2hSpecial u.succ.castSucc) (hsz t) 16 = true := by
  decide +kernel

theorem colCheck_sound (t0 t1 t2 : Fin 7) (P : ℕ)
    (hc : colCheck 32 t0 t1 t2 (hsz t0) (hsz t1) (hsz t2) P = true) (y0 y1 y2 : ℕ)
    (hy0 : y0 < hsz t0) (hy1 : y1 < hsz t1) (hy2 : y2 < hsz t2) :
    (∀ s : Fin 12, (s = 5 ∨ s = 10) →
      ∑ z0 ∈ Finset.range (hsz t0), ∑ z1 ∈ Finset.range (hsz t1), ∑ z2 ∈ Finset.range (hsz t2),
        aEnt t0 (x2hSpecial s) y0 z0 * (aEnt t1 (x2hSpecial s) y1 z1 * (aEnt t2 (x2hSpecial s) y2 z2 *
          ent 11 10 P ((z0 * hsz t1 + z1) * hsz t2 + z2))) =
        -ent 11 10 P ((y0 * hsz t1 + y1) * hsz t2 + y2)) ∧
    ∑ u : Fin 10, ∑ z0 ∈ Finset.range (hsz t0), ∑ z1 ∈ Finset.range (hsz t1), ∑ z2 ∈ Finset.range (hsz t2),
        aEnt t0 (x2hSpecial u.succ.castSucc) y0 z0 * (aEnt t1 (x2hSpecial u.succ.castSucc) y1 z1 *
          (aEnt t2 (x2hSpecial u.succ.castSucc) y2 z2 * ent 11 10 P ((z0 * hsz t1 + z1) * hsz t2 + z2))) =
        2 * ent 11 10 P ((y0 * hsz t1 + y1) * hsz t2 + y2) := by
  have hpos : ∀ t : Fin 7, 1 ≤ hsz t := by decide
  have h0 := hpos t0
  have h1 := hpos t1
  have h2 := hpos t2
  have hk : (y0 * hsz t1 + y1) * hsz t2 + y2 < hsz t0 * hsz t1 * hsz t2 := by
    have := site_idx_lt (hsz t0) (hsz t1) (hsz t2) y0 y1 y2 hy0 hy1 hy2
    rwa [← Nat.mul_assoc] at this
  have hsnd := fun u : Fin 10 => tApply_sound 32 (x2hSpecial u.succ.castSucc) t0 t1 t2 (hsz t0) (hsz t1)
    (hsz t2) P (by norm_num) h0 h1 h2 (x2hTranspRows u t0) (x2hTranspRows u t1) (x2hTranspRows u t2)
  unfold colCheck at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h5, h10⟩, hT⟩ := hc
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases hs with rfl | rfl
    · have e := Nat.eq_of_beq_eq_true h5
      have hs5 := (hsnd 4).2.2 y0 hy0 y1 hy1 y2 hy2
      have hidx : ((4 : Fin 10).succ.castSucc : Fin 12) = 5 := rfl
      rw [hidx] at hs5
      rw [← hs5, e, negSpread_ent 32 _ P (by norm_num) _ hk]
    · have e := Nat.eq_of_beq_eq_true h10
      have hs10 := (hsnd 9).2.2 y0 hy0 y1 hy1 y2 hy2
      have hidx : ((9 : Fin 10).succ.castSucc : Fin 12) = 10 := rfl
      rw [hidx] at hs10
      rw [← hs10, e, negSpread_ent 32 _ P (by norm_num) _ hk]
  · have hlin : ∀ k < hsz t0 * hsz t1 * hsz t2, |∑ a : Fin 10, (((fun _ : Fin 10 => 3) a : ℕ) - (2 : ℤ) ^ 1) *
        ent 32 (32 - 1) ((fun u : Fin 10 => tApply 32 (x2hSpecial u.succ.castSucc) t0 t1 t2 (hsz t0) (hsz t1)
          (hsz t2) P) a) k| < 2 ^ (32 - 1) := by
      intro k hk'
      calc |∑ a : Fin 10, (((fun _ : Fin 10 => 3) a : ℕ) - (2 : ℤ) ^ 1) *
            ent 32 (32 - 1) ((fun u : Fin 10 => tApply 32 (x2hSpecial u.succ.castSucc) t0 t1 t2 (hsz t0) (hsz t1)
              (hsz t2) P) a) k|
          ≤ ∑ a : Fin 10, |(((fun _ : Fin 10 => 3) a : ℕ) - (2 : ℤ) ^ 1) *
            ent 32 (32 - 1) ((fun u : Fin 10 => tApply 32 (x2hSpecial u.succ.castSucc) t0 t1 t2 (hsz t0) (hsz t1)
              (hsz t2) P) a) k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin 10, (2 ^ 22 : ℤ) := by
            apply Finset.sum_le_sum
            intro a _
            have hb := (hsnd a).2.1 k hk'
            have e3 : (((fun _ : Fin 10 => 3) a : ℕ) : ℤ) - (2 : ℤ) ^ 1 = 1 := by norm_num
            rw [e3, one_mul]
            exact hb
        _ < 2 ^ (32 - 1) := by norm_num [Finset.sum_const]
    have hax := natAxpy_contract 32 (hsz t0 * hsz t1 * hsz t2) 1 (fun _ : Fin 10 => 3)
      (fun u : Fin 10 => tApply 32 (x2hSpecial u.succ.castSucc) t0 t1 t2 (hsz t0) (hsz t1) (hsz t2) P)
      (2 * hsSpreadW 32 (hsz t0 * hsz t1 * hsz t2) P - offset 32 (32 - 1) (hsz t0 * hsz t1 * hsz t2))
      (by norm_num) (fun u => (hsnd u).1) hlin hT _ hk
    rw [dblSpread_ent 32 _ P (by norm_num) _ hk] at hax
    rw [← hax]
    apply Finset.sum_congr rfl
    intro u _
    rw [(hsnd u).2.2 y0 hy0 y1 hy1 y2 hy2]
    norm_num

end ThreeCopyQutritWerner.X2Sites

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-- The three transposition identities for every column of an h image (kernel check). -/
def keyCheck (b : x2Key 0) : Bool :=
  (List.range (x2KeySize 0 b)).all fun c =>
    colCheck 32 (x2hTau b).1 (x2hTau b).2.1 (x2hTau b).2.2 (hsz (x2hTau b).1) (hsz (x2hTau b).2.1)
      (hsz (x2hTau b).2.2) (x2JCols (x2KeyGlobal 0 b) c)

end ThreeCopyQutritWerner.X2Sites
