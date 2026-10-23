module

public import ThreeCopyQutritWerner.CertificateX2SitesUnits
public import ThreeCopyQutritWerner.CertificateX2Trans

@[expose] public section


/-!
# The per-site dictionary identities

For `s = 1, 2` and every unit `u` of sector `s`, the sector-0 compression of the unit weight
`x2SitesW s u` is the column `u` of `x2Qu D s` (`x2sDict1M`, `x2sDict2M`, in CertificateX2SitesDictFacts),
for any `X2Data` with the exact parity transfers `D.transS = X2.x2TransS`, `D.transA = X2.x2TransA`.

Route: `x2Qu D s v u = transS (sIdx v) (sIdx u) · c(u) + sgn v · transA (aIdx v) (aIdx u) · sgn u / 2`
(`x2Qu_apply`, from the bridge's definitions). The kernel computes, for every `u`, the packed
column `qpack s u` of `2 den_s x2Qu D s (·, u)` (`qformN`, from packed copies of the numerator tables) and checks `∑_p 2 Wnum_s[p, u] · C_0(piv p) = qpack s u` by natural axpy.
-/

set_option maxRecDepth 100000

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner.X2Sites

open X2

/-! ## `x2Qu` in closed form -/

theorem x2Select_inl (s : Fin 3) (l : Fin 282) (u : X2U s) :
    x2Select s (Sum.inl l) u =
      if x2SIdx s u.1 u.2.1 u.2.2 = l then (if (u.2.1 : ℕ) = u.2.2 then 1 else 1 / 2) else 0 := rfl

theorem x2Select_inr (s : Fin 3) (l : Fin 231) (u : X2U s) :
    x2Select s (Sum.inr l) u = if x2AIdx s u.1 u.2.1 u.2.2 = l then x2Sgn u.2.1 u.2.2 / 2 else 0 := rfl

theorem x2Qu_apply (D : X2Data) (s : Fin 3) (v : X2U 0) (u : X2U s) :
    x2Qu D s v u =
      D.transS s (x2SIdx 0 v.1 v.2.1 v.2.2) (x2SIdx s u.1 u.2.1 u.2.2) *
          (if (u.2.1 : ℕ) = u.2.2 then 1 else 1 / 2) +
        x2Sgn v.2.1 v.2.2 * D.transA s (x2AIdx 0 v.1 v.2.1 v.2.2) (x2AIdx s u.1 u.2.1 u.2.2) *
          (x2Sgn u.2.1 u.2.2 / 2) := by
  have h1 : ∀ P : X2P, (x2Expand 0 * x2ParityTransfer D s) v P =
      x2ParityTransfer D s (Sum.inl (x2SIdx 0 v.1 v.2.1 v.2.2)) P +
        x2Sgn v.2.1 v.2.2 * x2ParityTransfer D s (Sum.inr (x2AIdx 0 v.1 v.2.1 v.2.2)) P := by
    intro P
    rw [Matrix.mul_apply]
    exact x2_sum_expand v (fun P' => x2ParityTransfer D s P' P)
  unfold x2Qu
  rw [Matrix.mul_apply]
  simp only [h1]
  rw [Fintype.sum_sum_type]
  simp only [x2ParityTransfer_ll, x2ParityTransfer_lr, x2ParityTransfer_rl, x2ParityTransfer_rr,
    mul_zero, add_zero, zero_add, x2Select_inl, x2Select_inr, mul_ite, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  all_goals ring

/-! ## Packed copies of row tables -/

/-- `∑_j r_j 2^(W j)`. -/
def packRow (W : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.add x (Nat.shiftLeft (packRow W xs) W)

/-- `∑_i packRow (row i) 2^(W n i)`. -/
def packRows (W n : ℕ) : List (List ℕ) → ℕ
  | [] => 0
  | r :: rs => Nat.add (packRow W r) (Nat.shiftLeft (packRows W n rs) (Nat.mul W n))

theorem packRow_eq (W : ℕ) : ∀ r : List ℕ,
    packRow W r = ∑ j ∈ Finset.range r.length, r.getD j 0 * 2 ^ (W * j)
  | [] => rfl
  | x :: xs => by
    show Nat.add x (Nat.shiftLeft (packRow W xs) W) = _
    rw [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, packRow_eq W xs, List.length_cons,
      Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, pow_zero, Nat.mul_one]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.mul_assoc, ← pow_add]
    congr 2
    all_goals ring

theorem packRow_lt (W : ℕ) (r : List ℕ) (hb : ∀ x ∈ r, x < 2 ^ W) :
    packRow W r < 2 ^ (W * r.length) := by
  rw [packRow_eq, pow_mul]
  have hf : ∀ s, r.getD s 0 < 2 ^ W := by
    intro s
    by_cases h : s < r.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hb _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]
      positivity
  have := sum_digits_lt (2 ^ W) (fun s => r.getD s 0) hf r.length
  simpa only [pow_mul] using this

theorem ext_packRow (W : ℕ) (r : List ℕ) (hb : ∀ x ∈ r, x < 2 ^ W) (j : ℕ) (hj : j < r.length) :
    ext (packRow W r) W j = r.getD j 0 := by
  rw [ext_eq, packRow_eq]
  have hf : ∀ s, r.getD s 0 < 2 ^ W := by
    intro s
    by_cases h : s < r.length
    · rw [List.getD_eq_getElem _ _ h]
      exact hb _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]
      positivity
  have h := sum_digit (2 ^ W) r.length (fun s => r.getD s 0) (by positivity) hf j hj
  simpa only [pow_mul] using h

theorem packRows_eq (W n : ℕ) : ∀ rows : List (List ℕ),
    packRows W n rows = ∑ i ∈ Finset.range rows.length, packRow W (rows.getD i []) * 2 ^ (W * n * i)
  | [] => rfl
  | r :: rs => by
    show Nat.add (packRow W r) (Nat.shiftLeft (packRows W n rs) (Nat.mul W n)) = _
    rw [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.mul_eq, packRows_eq W n rs,
      List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, pow_zero, Nat.mul_one]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.mul_assoc, ← pow_add]
    congr 2
    all_goals ring

theorem ext_packRows (W n : ℕ) (rows : List (List ℕ)) (hl : ∀ r ∈ rows, r.length = n)
    (hb : ∀ r ∈ rows, ∀ x ∈ r, x < 2 ^ W) (i : ℕ) (hi : i < rows.length) :
    ext (packRows W n rows) (Nat.mul W n) i = packRow W (rows.getD i []) := by
  rw [Nat.mul_eq, ext_eq, packRows_eq]
  have hmem : ∀ s, s < rows.length → rows.getD s [] ∈ rows := by
    intro s hs
    rw [List.getD_eq_getElem _ _ hs]
    exact List.getElem_mem hs
  have hf : ∀ s, packRow W (rows.getD s []) < 2 ^ (W * n) := by
    intro s
    by_cases h : s < rows.length
    · have := packRow_lt W (rows.getD s []) (hb _ (hmem s h))
      rwa [hl _ (hmem s h)] at this
    · rw [List.getD_eq_default _ _ (by omega)]
      show 0 < 2 ^ (W * n)
      positivity
  have h := sum_digit (2 ^ (W * n)) rows.length (fun s => packRow W (rows.getD s [])) (by positivity)
    hf i hi
  simpa only [pow_mul] using h

/-! ## Numerators from the packed tables -/

/-- Packed S table of sector `s` (32-bit slots, row-major). -/
noncomputable def tsPack (s : ℕ) : ℕ := packRows 32 282 (transSRows s)

/-- Packed A table of sector `s`. -/
noncomputable def taPack (s : ℕ) : ℕ := packRows 32 231 (transARows s)

/-- `Snum_s[i][j]` read from the packed table. -/
noncomputable def numSP (s i j : ℕ) : ℤ := (ext (ext (tsPack s) (Nat.mul 32 282) i) 32 j : ℤ) - 2 ^ 31

/-- `Anum_s[i][j]` read from the packed table. -/
noncomputable def numAP (s i j : ℕ) : ℤ := (ext (ext (taPack s) (Nat.mul 32 231) i) 32 j : ℤ) - 2 ^ 31

theorem ext_lt (T WY c : ℕ) : ext T WY c < 2 ^ WY := by
  rw [ext_eq]
  exact Nat.mod_lt _ (by positivity)

theorem numSP_abs (s i j : ℕ) : |numSP s i j| ≤ 2 ^ 31 := by
  unfold numSP
  have h := ext_lt (ext (tsPack s) (Nat.mul 32 282) i) 32 j
  rw [abs_le]
  have h1 : ((ext (ext (tsPack s) (Nat.mul 32 282) i) 32 j : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast h
  have h2 : (0 : ℤ) ≤ ((ext (ext (tsPack s) (Nat.mul 32 282) i) 32 j : ℕ) : ℤ) := Int.natCast_nonneg _
  constructor <;> linarith

theorem numAP_abs (s i j : ℕ) : |numAP s i j| ≤ 2 ^ 31 := by
  unfold numAP
  have h := ext_lt (ext (taPack s) (Nat.mul 32 231) i) 32 j
  rw [abs_le]
  have h1 : ((ext (ext (taPack s) (Nat.mul 32 231) i) 32 j : ℕ) : ℤ) < 2 ^ 32 := by exact_mod_cast h
  have h2 : (0 : ℤ) ≤ ((ext (ext (taPack s) (Nat.mul 32 231) i) 32 j : ℕ) : ℤ) := Int.natCast_nonneg _
  constructor <;> linarith

/-! ## Integer labels and decoding of flat unit slots -/

/-- Integer sign of a pair. -/
def sgnZ (a b : ℕ) : ℤ := if a < b then 1 else if b < a then -1 else 0

theorem sgnZ_cast (a b : ℕ) : ((sgnZ a b : ℤ) : ℚ) = x2Sgn a b := by
  unfold sgnZ x2Sgn
  split_ifs <;> simp

theorem sgnZ_abs (a b : ℕ) : |sgnZ a b| ≤ 1 := by
  unfold sgnZ
  split_ifs <;> simp

/-- Type of a flat unit slot. -/
def typeU (s : Fin 3) (k : ℕ) : Fin 8 :=
  if k < x2sOffU s 1 then 0 else if k < x2sOffU s 2 then 1 else if k < x2sOffU s 3 then 2 else
  if k < x2sOffU s 4 then 3 else if k < x2sOffU s 5 then 4 else if k < x2sOffU s 6 then 5 else
  if k < x2sOffU s 7 then 6 else 7

/-- Decoding of a flat unit slot into `(t, a, b)`. -/
def decU (s : Fin 3) (k : ℕ) : Fin 8 × ℕ × ℕ :=
  (typeU s k, (k - x2sOffU s (typeU s k)) / x2Mult s (typeU s k),
    (k - x2sOffU s (typeU s k)) % x2Mult s (typeU s k))

theorem decU_flat : ∀ s : Fin 3, ∀ u : X2U s,
    decU s (x2sFlatU s u) = (u.1, (u.2.1 : ℕ), (u.2.2 : ℕ)) := by
  decide +kernel

/-- `2 den_s x2Qu D s (v, u)` at the flat slots `k` of `v` and `j` of `u`. -/
noncomputable def qformN (s : Fin 3) (k j : ℕ) : ℤ :=
  (if (decU s j).2.1 = (decU s j).2.2 then 2 else 1) *
      numSP s (x2SIdx 0 (decU 0 k).1 (decU 0 k).2.1 (decU 0 k).2.2)
        (x2SIdx s (decU s j).1 (decU s j).2.1 (decU s j).2.2) +
    sgnZ (decU 0 k).2.1 (decU 0 k).2.2 * sgnZ (decU s j).2.1 (decU s j).2.2 *
      numAP s (x2AIdx 0 (decU 0 k).1 (decU 0 k).2.1 (decU 0 k).2.2)
        (x2AIdx s (decU s j).1 (decU s j).2.1 (decU s j).2.2)

theorem qformN_abs (s : Fin 3) (k j : ℕ) : |qformN s k j| < 2 ^ 47 := by
  unfold qformN
  have h1 := numSP_abs s (x2SIdx 0 (decU 0 k).1 (decU 0 k).2.1 (decU 0 k).2.2)
    (x2SIdx s (decU s j).1 (decU s j).2.1 (decU s j).2.2)
  have h2 := numAP_abs s (x2AIdx 0 (decU 0 k).1 (decU 0 k).2.1 (decU 0 k).2.2)
    (x2AIdx s (decU s j).1 (decU s j).2.1 (decU s j).2.2)
  have h3 := sgnZ_abs (decU 0 k).2.1 (decU 0 k).2.2
  have h4 := sgnZ_abs (decU s j).2.1 (decU s j).2.2
  have hc : |(if (decU s j).2.1 = (decU s j).2.2 then (2 : ℤ) else 1)| ≤ 2 := by
    split_ifs <;> norm_num
  calc |(if (decU s j).2.1 = (decU s j).2.2 then (2 : ℤ) else 1) *
        numSP s (x2SIdx 0 (decU 0 k).1 (decU 0 k).2.1 (decU 0 k).2.2)
          (x2SIdx s (decU s j).1 (decU s j).2.1 (decU s j).2.2) +
      sgnZ (decU 0 k).2.1 (decU 0 k).2.2 * sgnZ (decU s j).2.1 (decU s j).2.2 *
        numAP s (x2AIdx 0 (decU 0 k).1 (decU 0 k).2.1 (decU 0 k).2.2)
          (x2AIdx s (decU s j).1 (decU s j).2.1 (decU s j).2.2)|
      ≤ 2 * 2 ^ 31 + 1 * 1 * 2 ^ 31 := by
        refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul hc h1 (abs_nonneg _) (by norm_num)
        · rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul h3 h4 (abs_nonneg _) (by norm_num)) h2 (abs_nonneg _) (by norm_num)
    _ < 2 ^ 47 := by norm_num

/-- Packed column `∑_{k < n} (2^47 + qformN s k j) 2^(48 k)`, by a kernel-friendly fold. -/
noncomputable def qpackAux (s : Fin 3) (j : ℕ) : ℕ → ℕ :=
  @Nat.rec (fun _ => ℕ) 0 (fun k acc => Nat.add acc
    (Nat.mul (Int.toNat (2 ^ 47 + qformN s k j)) (Nat.shiftLeft 1 (Nat.mul 48 k))))

theorem qpackAux_eq (s : Fin 3) (j : ℕ) (n : ℕ) :
    qpackAux s j n = ∑ k ∈ Finset.range n, Int.toNat (2 ^ 47 + qformN s k j) * 2 ^ (48 * k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    show Nat.add (qpackAux s j n) (Nat.mul _ (Nat.shiftLeft 1 (Nat.mul 48 n))) = _
    rw [Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.mul_eq]

theorem ent_qpack (s : Fin 3) (j k : ℕ) (hk : k < 513) :
    ent 48 (48 - 1) (qpackAux s j 513) k = qformN s k j := by
  have hq := qformN_abs
  have hf : ∀ k', Int.toNat (2 ^ 47 + qformN s k' j) < 2 ^ 48 := by
    intro k'
    have := hq s k' j
    rw [abs_lt] at this
    have h1 : (2 : ℤ) ^ 47 + qformN s k' j < 2 ^ 48 := by
      have h48 : (2 : ℤ) ^ 48 = 2 ^ 47 + 2 ^ 47 := by norm_num
      linarith [this.2]
    have h0' : (0 : ℤ) ≤ 2 ^ 47 + qformN s k' j := by linarith [this.1]
    have h2 : ((Int.toNat (2 ^ 47 + qformN s k' j) : ℕ) : ℤ) < 2 ^ 48 := by
      rw [Int.toNat_of_nonneg h0']
      exact h1
    exact_mod_cast h2
  have hd := sum_digit (2 ^ 48) 513 (fun k' => Int.toNat (2 ^ 47 + qformN s k' j)) (by positivity) hf k hk
  unfold ent dig
  rw [qpackAux_eq]
  simp only [pow_mul]
  rw [hd]
  have h0 : (0 : ℤ) ≤ 2 ^ 47 + qformN s k j := by
    have := hq s k j
    rw [abs_lt] at this
    linarith [this.1]
  rw [Int.toNat_of_nonneg h0]
  norm_num

/-! ## Kernel checks -/

theorem trans_bounds : (transS1Tab.all (·.all (fun x => Nat.blt x (2 ^ 32)))) &&
    (transS2Tab.all (·.all (fun x => Nat.blt x (2 ^ 32)))) &&
    (transA1Tab.all (·.all (fun x => Nat.blt x (2 ^ 32)))) &&
    (transA2Tab.all (·.all (fun x => Nat.blt x (2 ^ 32)))) = true := by
  decide +kernel

end ThreeCopyQutritWerner.X2Sites
