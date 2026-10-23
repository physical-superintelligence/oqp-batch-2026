module

public import ThreeCopyQutritWerner.CertificateX2InputBlocks
public import ThreeCopyQutritWerner.CertificateX2InputSym
public import ThreeCopyQutritWerner.CertificateX2Data
public import ThreeCopyQutritWerner.CertificateX2OutLemmas

@[expose] public section


/-!
# Input stage: stabilizer invariance of the input blocks of degree-1 keys

For a key whose sorted type triple has two equal adjacent types, the image `J` is symmetric
(kind 0) or antisymmetric (kind 1) under the swap of those two sites. `x2JColOK` checks this on one
packed image column (11-bit digits, offset `2^10`, flat order): runs over the last site for the
symmetric swap of sites 0 and 1, digits of the site-0 slabs otherwise. The kernel evaluates
`x2JKeyOK` per key in the generated modules `CertificateX2InputJChk*`. From the check:

* the sign law of the concrete images (`x2Image_swap01`, `x2Image_swap12`), hence of
  `GJ = (G ⊗ G ⊗ G) J` (`x2GJ_swap01`, `x2GJ_swap12` of CertificateX2InputBlocks);
* `x2InputBlock_inv_of_ok`: for a degree-1 key, the input block `GJ N GJᵀ` is invariant under every
  site permutation that fixes the (sorted) type triple, for EVERY source `N`. This is the hypothesis
  `hinv` of `x2FullTensor_sorted` for the degree-1 keys.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Kernel checks on one packed image column -/

/-- Swap of sites 0, 1 (`m₀ = m₁ = m`), symmetric image: the runs over site 2 agree. -/
def jsw01S (col m m2 : ℕ) : Bool :=
  (List.range m).all fun y0 => (List.range y0).all fun y1 =>
    runOf 11 m2 (y1 * m2) (runOf 11 (m * m2) (y0 * (m * m2)) col) ==
      runOf 11 m2 (y0 * m2) (runOf 11 (m * m2) (y1 * (m * m2)) col)

/-- Swap of sites 0, 1, antisymmetric image: swapped digits sum to `2^11` (diagonal included). -/
def jsw01A (col m m2 : ℕ) : Bool :=
  (List.range m).all fun y0 => (List.range (y0 + 1)).all fun y1 => (List.range m2).all fun y2 =>
    dig 11 (runOf 11 (m * m2) (y0 * (m * m2)) col) (y1 * m2 + y2) +
      dig 11 (runOf 11 (m * m2) (y1 * (m * m2)) col) (y0 * m2 + y2) == 2048

/-- Swap of sites 1, 2 (`m₁ = m₂ = m`), symmetric image: each site-0 slab is a symmetric matrix. -/
def jsw12S (col m0 m : ℕ) : Bool :=
  (List.range m0).all fun y0 => (List.range m).all fun y1 => (List.range y1).all fun y2 =>
    dig 11 (runOf 11 (m * m) (y0 * (m * m)) col) (y1 * m + y2) ==
      dig 11 (runOf 11 (m * m) (y0 * (m * m)) col) (y2 * m + y1)

/-- Swap of sites 1, 2, antisymmetric image (diagonal included). -/
def jsw12A (col m0 m : ℕ) : Bool :=
  (List.range m0).all fun y0 => (List.range m).all fun y1 => (List.range (y1 + 1)).all fun y2 =>
    dig 11 (runOf 11 (m * m) (y0 * (m * m)) col) (y1 * m + y2) +
      dig 11 (runOf 11 (m * m) (y0 * (m * m)) col) (y2 * m + y1) == 2048

/-! ### Soundness of the column checks -/

theorem jidx_lt (y1 y2 m m2 : ℕ) (h1 : y1 < m) (h2 : y2 < m2) : y1 * m2 + y2 < m * m2 := by
  calc y1 * m2 + y2 < y1 * m2 + m2 := by omega
    _ = (y1 + 1) * m2 := by ring
    _ ≤ m * m2 := Nat.mul_le_mul_right m2 h1

theorem dig_slab2 (col m m2 u v y2 : ℕ) (hv : v < m) (h2 : y2 < m2) :
    dig 11 (runOf 11 (m * m2) (u * (m * m2)) col) (v * m2 + y2) = dig 11 col ((u * m + v) * m2 + y2) := by
  rw [dig_runOf 11 (m * m2) _ col _ (jidx_lt v y2 m m2 hv h2)]
  congr 1
  ring

theorem dig_run2 (col m m2 u v y2 : ℕ) (hv : v < m) (h2 : y2 < m2) :
    dig 11 (runOf 11 m2 (v * m2) (runOf 11 (m * m2) (u * (m * m2)) col)) y2 =
      dig 11 col ((u * m + v) * m2 + y2) := by
  rw [dig_runOf 11 m2 _ _ y2 h2, dig_slab2 col m m2 u v y2 hv h2]

theorem jsw01S_sound (col m m2 : ℕ) (h : jsw01S col m m2 = true) (y0 y1 y2 : ℕ) (h0 : y0 < m)
    (h1 : y1 < m) (h2 : y2 < m2) :
    dig 11 col ((y1 * m + y0) * m2 + y2) = dig 11 col ((y0 * m + y1) * m2 + y2) := by
  have core : ∀ u v, u < m → v < u →
      dig 11 col ((u * m + v) * m2 + y2) = dig 11 col ((v * m + u) * m2 + y2) := by
    intro u v hu hv
    unfold jsw01S at h
    have hu' := List.all_eq_true.mp h u (List.mem_range.mpr hu)
    have hv' := List.all_eq_true.mp hu' v (List.mem_range.mpr hv)
    have he := congrArg (fun R => dig 11 R y2) (beq_iff_eq.mp hv')
    rw [dig_run2 col m m2 u v y2 (by omega) h2, dig_run2 col m m2 v u y2 hu h2] at he
    exact he
  rcases lt_trichotomy y0 y1 with hlt | heq | hgt
  · exact core y1 y0 h1 hlt
  · subst heq
    rfl
  · exact (core y0 y1 h0 hgt).symm

theorem jsw01A_sound (col m m2 : ℕ) (h : jsw01A col m m2 = true) (y0 y1 y2 : ℕ) (h0 : y0 < m)
    (h1 : y1 < m) (h2 : y2 < m2) :
    dig 11 col ((y1 * m + y0) * m2 + y2) + dig 11 col ((y0 * m + y1) * m2 + y2) = 2048 := by
  have core : ∀ u v, u < m → v ≤ u →
      dig 11 col ((u * m + v) * m2 + y2) + dig 11 col ((v * m + u) * m2 + y2) = 2048 := by
    intro u v hu hv
    unfold jsw01A at h
    have hu' := List.all_eq_true.mp h u (List.mem_range.mpr hu)
    have hv' := List.all_eq_true.mp hu' v (List.mem_range.mpr (by omega))
    have hy := List.all_eq_true.mp hv' y2 (List.mem_range.mpr h2)
    have he := beq_iff_eq.mp hy
    rw [dig_slab2 col m m2 u v y2 (by omega) h2, dig_slab2 col m m2 v u y2 hu h2] at he
    exact he
  rcases Nat.lt_or_ge y1 y0 with hgt | hle
  · rw [add_comm]
    exact core y0 y1 h0 hgt.le
  · exact core y1 y0 h1 hle

theorem jsw12S_sound (col m0 m : ℕ) (h : jsw12S col m0 m = true) (y0 y1 y2 : ℕ) (h0 : y0 < m0)
    (h1 : y1 < m) (h2 : y2 < m) :
    dig 11 col ((y0 * m + y2) * m + y1) = dig 11 col ((y0 * m + y1) * m + y2) := by
  have core : ∀ u v, u < m → v < u →
      dig 11 col ((y0 * m + u) * m + v) = dig 11 col ((y0 * m + v) * m + u) := by
    intro u v hu hv
    unfold jsw12S at h
    have h0' := List.all_eq_true.mp h y0 (List.mem_range.mpr h0)
    have hu' := List.all_eq_true.mp h0' u (List.mem_range.mpr hu)
    have hv' := List.all_eq_true.mp hu' v (List.mem_range.mpr hv)
    have he := beq_iff_eq.mp hv'
    rw [dig_slab2 col m m y0 u v hu (by omega), dig_slab2 col m m y0 v u (by omega) hu] at he
    exact he
  rcases lt_trichotomy y1 y2 with hlt | heq | hgt
  · exact core y2 y1 h2 hlt
  · subst heq
    rfl
  · exact (core y1 y2 h1 hgt).symm

theorem jsw12A_sound (col m0 m : ℕ) (h : jsw12A col m0 m = true) (y0 y1 y2 : ℕ) (h0 : y0 < m0)
    (h1 : y1 < m) (h2 : y2 < m) :
    dig 11 col ((y0 * m + y2) * m + y1) + dig 11 col ((y0 * m + y1) * m + y2) = 2048 := by
  have core : ∀ u v, u < m → v ≤ u →
      dig 11 col ((y0 * m + u) * m + v) + dig 11 col ((y0 * m + v) * m + u) = 2048 := by
    intro u v hu hv
    unfold jsw12A at h
    have h0' := List.all_eq_true.mp h y0 (List.mem_range.mpr h0)
    have hu' := List.all_eq_true.mp h0' u (List.mem_range.mpr hu)
    have hv' := List.all_eq_true.mp hu' v (List.mem_range.mpr (by omega))
    have he := beq_iff_eq.mp hv'
    rw [dig_slab2 col m m y0 u v hu (by omega), dig_slab2 col m m y0 v u (by omega) hu] at he
    exact he
  rcases Nat.lt_or_ge y1 y2 with hgt | hle
  · exact core y2 y1 h2 hgt.le
  · rw [add_comm]
    exact core y1 y2 h1 hle

theorem ent_eq_of_dig_eq (col i j : ℕ) (h : dig 11 col i = dig 11 col j) :
    ent 11 10 col i = 1 * ent 11 10 col j := by
  rw [one_mul]
  unfold ent
  rw [h]

theorem ent_neg_of_dig_sum (col i j : ℕ) (h : dig 11 col i + dig 11 col j = 2048) :
    ent 11 10 col i = -1 * ent 11 10 col j := by
  unfold ent
  have h' : ((dig 11 col i : ℕ) : ℤ) + ((dig 11 col j : ℕ) : ℤ) = 2048 := by exact_mod_cast h
  have h2 : (2 : ℤ) ^ 10 = 1024 := by norm_num
  rw [h2]
  linarith

/-! ### The concrete images in natural coordinates -/

theorem x2Get3_image_concrete (s : Fin 3) (k : x2Key s) (y0 y1 y2 : ℕ) (d : x2Col s k) :
    x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d =
      if y0 < x2KeyMult s k 0 ∧ y1 < x2KeyMult s k 1 ∧ y2 < x2KeyMult s k 2 then
        ((ent 11 10 (x2JCols (x2KeyGlobal s k) d)
          ((y0 * x2KeyMult s k 1 + y1) * x2KeyMult s k 2 + y2) : ℤ) : ℚ)
      else 0 := by
  unfold x2Get3
  split_ifs <;> rfl

theorem x2Image_swap01 (s : Fin 3) (k : x2Key s) (ε : ℤ) (hm : x2KeyMult s k 0 = x2KeyMult s k 1)
    (h : ∀ y0 y1 y2 c, y0 < x2KeyMult s k 0 → y1 < x2KeyMult s k 0 → y2 < x2KeyMult s k 2 →
      c < x2KeySize s k →
      ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y1 * x2KeyMult s k 0 + y0) * x2KeyMult s k 2 + y2) =
        ε * ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y0 * x2KeyMult s k 0 + y1) * x2KeyMult s k 2 + y2))
    (y0 y1 y2 : ℕ) (d : x2Col s k) :
    x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y1 y0 y2 d =
      (ε : ℚ) * x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d := by
  rw [x2Get3_image_concrete, x2Get3_image_concrete, ← hm]
  by_cases hy : y0 < x2KeyMult s k 0 ∧ y1 < x2KeyMult s k 0 ∧ y2 < x2KeyMult s k 2
  · rw [if_pos ⟨hy.2.1, hy.1, hy.2.2⟩, if_pos hy, h y0 y1 y2 d hy.1 hy.2.1 hy.2.2 d.isLt, Int.cast_mul]
  · rw [if_neg (fun h' => hy ⟨h'.2.1, h'.1, h'.2.2⟩), if_neg hy, mul_zero]

theorem x2Image_swap12 (s : Fin 3) (k : x2Key s) (ε : ℤ) (hm : x2KeyMult s k 1 = x2KeyMult s k 2)
    (h : ∀ y0 y1 y2 c, y0 < x2KeyMult s k 0 → y1 < x2KeyMult s k 1 → y2 < x2KeyMult s k 1 →
      c < x2KeySize s k →
      ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y0 * x2KeyMult s k 1 + y2) * x2KeyMult s k 1 + y1) =
        ε * ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y0 * x2KeyMult s k 1 + y1) * x2KeyMult s k 1 + y2))
    (y0 y1 y2 : ℕ) (d : x2Col s k) :
    x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y0 y2 y1 d =
      (ε : ℚ) * x2Get3 ((x2DataConcrete.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d := by
  rw [x2Get3_image_concrete, x2Get3_image_concrete, ← hm]
  by_cases hy : y0 < x2KeyMult s k 0 ∧ y1 < x2KeyMult s k 1 ∧ y2 < x2KeyMult s k 1
  · rw [if_pos ⟨hy.1, hy.2.2, hy.2.1⟩, if_pos hy, h y0 y1 y2 d hy.1 hy.2.1 hy.2.2 d.isLt, Int.cast_mul]
  · rw [if_neg (fun h' => hy ⟨h'.1, h'.2.2, h'.2.1⟩), if_neg hy, mul_zero]

/-! ### The per-key check -/

/-- Sign of a degree-1 key's image under swaps of equal-type sites: `-1` for kind 1, else `1`. -/
def x2JSign (s : Fin 3) (k : x2Key s) : ℤ := if x2KeyKind s k = 1 then -1 else 1

/-- All sign-law checks on column `c` of key `k`. -/
noncomputable def x2JColOK (s : Fin 3) (k : x2Key s) (c : ℕ) : Bool :=
  (!(decide (x2KeyTypes s k 0 = x2KeyTypes s k 1)) ||
      (if x2KeyKind s k = 1 then jsw01A (x2JCols (x2KeyGlobal s k) c) (x2KeyMult s k 0) (x2KeyMult s k 2)
       else jsw01S (x2JCols (x2KeyGlobal s k) c) (x2KeyMult s k 0) (x2KeyMult s k 2))) &&
    (!(decide (x2KeyTypes s k 1 = x2KeyTypes s k 2)) ||
      (if x2KeyKind s k = 1 then jsw12A (x2JCols (x2KeyGlobal s k) c) (x2KeyMult s k 0) (x2KeyMult s k 1)
       else jsw12S (x2JCols (x2KeyGlobal s k) c) (x2KeyMult s k 0) (x2KeyMult s k 1)))

/-- All columns of a key (degree-2 keys are skipped: they are treated through their partner). -/
noncomputable def x2JKeyOK (s : Fin 3) (k : x2Key s) : Bool :=
  (x2KeyDegree s k == 2) || (List.range (x2KeySize s k)).all (x2JColOK s k)

/-- Columns `c₀ ≤ c < c₀ + n` of a key. -/
noncomputable def x2JColRangeOK (s : Fin 3) (k : x2Key s) (c0 n : ℕ) : Bool :=
  (List.range' c0 n).all (x2JColOK s k)

/-- Keys `lo ≤ k < lo + n` of a sector. -/
noncomputable def x2JKeyRangeOK (s : Fin 3) (lo n : ℕ) : Bool :=
  (List.range' lo n).all (fun kv => if h : kv < x2NumKeys s then x2JKeyOK s ⟨kv, h⟩ else true)

theorem x2JColRangeOK_mem (s : Fin 3) (k : x2Key s) (c0 n c : ℕ) (h : x2JColRangeOK s k c0 n = true)
    (h1 : c0 ≤ c) (h2 : c < c0 + n) : x2JColOK s k c = true :=
  List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem x2JKeyRangeOK_mem (s : Fin 3) (lo n : ℕ) (h : x2JKeyRangeOK s lo n = true) (k : x2Key s)
    (h1 : lo ≤ k.val) (h2 : k.val < lo + n) : x2JKeyOK s k = true := by
  have := List.all_eq_true.mp h k.val (List.mem_range'_1.mpr ⟨h1, h2⟩)
  rw [dif_pos k.isLt] at this
  exact this

theorem x2JKeyOK_of_cols (s : Fin 3) (k : x2Key s)
    (h : ∀ c, c < x2KeySize s k → x2JColOK s k c = true) : x2JKeyOK s k = true := by
  unfold x2JKeyOK
  rw [Bool.or_eq_true]
  right
  exact List.all_eq_true.mpr (fun c hc => h c (List.mem_range.mp hc))

theorem x2JColOK_law01 (s : Fin 3) (k : x2Key s) (c : ℕ) (hc : x2JColOK s k c = true)
    (ht : x2KeyTypes s k 0 = x2KeyTypes s k 1) (y0 y1 y2 : ℕ) (h0 : y0 < x2KeyMult s k 0)
    (h1 : y1 < x2KeyMult s k 0) (h2 : y2 < x2KeyMult s k 2) :
    ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y1 * x2KeyMult s k 0 + y0) * x2KeyMult s k 2 + y2) =
      x2JSign s k * ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y0 * x2KeyMult s k 0 + y1) * x2KeyMult s k 2 + y2) := by
  unfold x2JColOK at hc
  rw [Bool.and_eq_true] at hc
  have h1' := hc.1
  rw [decide_eq_true ht, Bool.not_true, Bool.false_or] at h1'
  unfold x2JSign
  by_cases hk : x2KeyKind s k = 1
  · rw [if_pos hk] at h1'
    rw [if_pos hk]
    exact ent_neg_of_dig_sum _ _ _ (jsw01A_sound _ _ _ h1' y0 y1 y2 h0 h1 h2)
  · rw [if_neg hk] at h1'
    rw [if_neg hk]
    exact ent_eq_of_dig_eq _ _ _ (jsw01S_sound _ _ _ h1' y0 y1 y2 h0 h1 h2)

theorem x2JColOK_law12 (s : Fin 3) (k : x2Key s) (c : ℕ) (hc : x2JColOK s k c = true)
    (ht : x2KeyTypes s k 1 = x2KeyTypes s k 2) (y0 y1 y2 : ℕ) (h0 : y0 < x2KeyMult s k 0)
    (h1 : y1 < x2KeyMult s k 1) (h2 : y2 < x2KeyMult s k 1) :
    ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y0 * x2KeyMult s k 1 + y2) * x2KeyMult s k 1 + y1) =
      x2JSign s k * ent 11 10 (x2JCols (x2KeyGlobal s k) c) ((y0 * x2KeyMult s k 1 + y1) * x2KeyMult s k 1 + y2) := by
  unfold x2JColOK at hc
  rw [Bool.and_eq_true] at hc
  have h2' := hc.2
  rw [decide_eq_true ht, Bool.not_true, Bool.false_or] at h2'
  unfold x2JSign
  by_cases hk : x2KeyKind s k = 1
  · rw [if_pos hk] at h2'
    rw [if_pos hk]
    exact ent_neg_of_dig_sum _ _ _ (jsw12A_sound _ _ _ h2' y0 y1 y2 h0 h1 h2)
  · rw [if_neg hk] at h2'
    rw [if_neg hk]
    exact ent_eq_of_dig_eq _ _ _ (jsw12S_sound _ _ _ h2' y0 y1 y2 h0 h1 h2)

/-! ### Invariance of `G M Gᵀ` and composition of the swaps -/

theorem x2Lookup_conj {p q r : ℕ} {κ : Type*} [Fintype κ] (G : Matrix (Fin p × Fin q × Fin r) κ ℚ)
    (M : Matrix κ κ ℚ) (a b : Fin 3 → ℕ) :
    x2Lookup (G * M * Gᵀ) a b =
      ∑ c, ∑ c', x2Get3 G (a 0) (a 1) (a 2) c * M c c' * x2Get3 G (b 0) (b 1) (b 2) c' := by
  unfold x2Lookup x2Get3
  by_cases ha : a 0 < p ∧ a 1 < q ∧ a 2 < r
  · by_cases hb : b 0 < p ∧ b 1 < q ∧ b 2 < r
    · rw [dif_pos ⟨ha, hb⟩]
      simp only [dif_pos ha, dif_pos hb]
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    · rw [dif_neg (fun h => hb h.2)]
      simp [dif_neg hb]
  · rw [dif_neg (fun h => ha h.1)]
    simp [dif_neg ha]

theorem x2Lookup_conj_inv {p q r : ℕ} {κ : Type*} [Fintype κ] (G : Matrix (Fin p × Fin q × Fin r) κ ℚ)
    (M : Matrix κ κ ℚ) (π : Fin 3 → Fin 3) (ε : ℚ) (hε : ε * ε = 1)
    (hG : ∀ (a : Fin 3 → ℕ) (c : κ),
      x2Get3 G (a (π 0)) (a (π 1)) (a (π 2)) c = ε * x2Get3 G (a 0) (a 1) (a 2) c)
    (a b : Fin 3 → ℕ) :
    x2Lookup (G * M * Gᵀ) (a ∘ π) (b ∘ π) = x2Lookup (G * M * Gᵀ) a b := by
  rw [x2Lookup_conj, x2Lookup_conj]
  simp only [Function.comp_apply, hG]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro c' _
  linear_combination (x2Get3 G (a 0) (a 1) (a 2) c * M c c' * x2Get3 G (b 0) (b 1) (b 2) c') * hε

theorem x2Perm3_comp0 (a : Fin 3 → ℕ) : a ∘ x2Perm3 0 = a := by
  funext i
  fin_cases i <;> rfl

theorem x2Perm3_comp3 (a : Fin 3 → ℕ) : a ∘ x2Perm3 3 = (a ∘ x2Perm3 2) ∘ x2Perm3 1 := by
  funext i
  fin_cases i <;> rfl

theorem x2Perm3_comp4 (a : Fin 3 → ℕ) : a ∘ x2Perm3 4 = (a ∘ x2Perm3 1) ∘ x2Perm3 2 := by
  funext i
  fin_cases i <;> rfl

theorem x2Perm3_comp5 (a : Fin 3 → ℕ) : a ∘ x2Perm3 5 = ((a ∘ x2Perm3 2) ∘ x2Perm3 1) ∘ x2Perm3 2 := by
  funext i
  fin_cases i <;> rfl

section stab

variable {p q r : ℕ} (M : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ) (t : Fin 3 → Fin 8)
  (h01 : t 0 = t 1 → ∀ a b : Fin 3 → ℕ, x2Lookup M (a ∘ x2Perm3 2) (b ∘ x2Perm3 2) = x2Lookup M a b)
  (h12 : t 1 = t 2 → ∀ a b : Fin 3 → ℕ, x2Lookup M (a ∘ x2Perm3 1) (b ∘ x2Perm3 1) = x2Lookup M a b)
  (a b : Fin 3 → ℕ)

include h01 h12

theorem x2Stab_case0 : x2Lookup M (a ∘ x2Perm3 0) (b ∘ x2Perm3 0) = x2Lookup M a b := by
  rw [x2Perm3_comp0 a, x2Perm3_comp0 b]

theorem x2Stab_case1 (hπ : t ∘ x2Perm3 1 = t) :
    x2Lookup M (a ∘ x2Perm3 1) (b ∘ x2Perm3 1) = x2Lookup M a b := by
  have e : t 2 = t 1 := congrFun hπ 1
  exact h12 e.symm a b

theorem x2Stab_case2 (hπ : t ∘ x2Perm3 2 = t) :
    x2Lookup M (a ∘ x2Perm3 2) (b ∘ x2Perm3 2) = x2Lookup M a b := by
  have e : t 1 = t 0 := congrFun hπ 0
  exact h01 e.symm a b

theorem x2Stab_case3 (hπ : t ∘ x2Perm3 3 = t) :
    x2Lookup M (a ∘ x2Perm3 3) (b ∘ x2Perm3 3) = x2Lookup M a b := by
  have e0 : t 1 = t 0 := congrFun hπ 0
  have e1 : t 2 = t 1 := congrFun hπ 1
  rw [x2Perm3_comp3 a, x2Perm3_comp3 b, h12 e1.symm (a ∘ x2Perm3 2) (b ∘ x2Perm3 2), h01 e0.symm a b]

theorem x2Stab_case4 (hπ : t ∘ x2Perm3 4 = t) :
    x2Lookup M (a ∘ x2Perm3 4) (b ∘ x2Perm3 4) = x2Lookup M a b := by
  have e1 : t 0 = t 1 := congrFun hπ 1
  have e2 : t 1 = t 2 := congrFun hπ 2
  rw [x2Perm3_comp4 a, x2Perm3_comp4 b, h01 e1 (a ∘ x2Perm3 1) (b ∘ x2Perm3 1), h12 e2 a b]

theorem x2Stab_case5 (ht : x2Sorted t) (hπ : t ∘ x2Perm3 5 = t) :
    x2Lookup M (a ∘ x2Perm3 5) (b ∘ x2Perm3 5) = x2Lookup M a b := by
  have e0 : t 2 = t 0 := congrFun hπ 0
  obtain ⟨s01, s12⟩ := ht
  have f01 : t 0 = t 1 := le_antisymm s01 (by rw [← e0]; exact s12)
  have f12 : t 1 = t 2 := f01.symm.trans e0.symm
  rw [x2Perm3_comp5 a, x2Perm3_comp5 b, h01 f01 _ _, h12 f12 _ _, h01 f01 a b]

end stab

/-- Invariance under the two adjacent swaps (when the corresponding types agree) gives invariance
under every site permutation fixing a sorted type triple. -/
theorem x2Lookup_stab_of_swaps {p q r : ℕ} (M : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ)
    (t : Fin 3 → Fin 8) (ht : x2Sorted t)
    (h01 : t 0 = t 1 → ∀ a b : Fin 3 → ℕ, x2Lookup M (a ∘ x2Perm3 2) (b ∘ x2Perm3 2) = x2Lookup M a b)
    (h12 : t 1 = t 2 → ∀ a b : Fin 3 → ℕ, x2Lookup M (a ∘ x2Perm3 1) (b ∘ x2Perm3 1) = x2Lookup M a b)
    (π : Fin 6) (hπ : t ∘ x2Perm3 π = t) (a b : Fin 3 → ℕ) :
    x2Lookup M (a ∘ x2Perm3 π) (b ∘ x2Perm3 π) = x2Lookup M a b := by
  fin_cases π
  · exact x2Stab_case0 M t h01 h12 a b
  · exact x2Stab_case1 M t h01 h12 a b hπ
  · exact x2Stab_case2 M t h01 h12 a b hπ
  · exact x2Stab_case3 M t h01 h12 a b hπ
  · exact x2Stab_case4 M t h01 h12 a b hπ
  · exact x2Stab_case5 M t h01 h12 a b ht hπ

/-! ### Stabilizer invariance of the input blocks of degree-1 keys -/

theorem x2JSign_sq (s : Fin 3) (k : x2Key s) : ((x2JSign s k : ℤ) : ℚ) * (x2JSign s k : ℚ) = 1 := by
  unfold x2JSign
  split_ifs <;> norm_num

theorem x2InputBlock_deg1 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (hdeg : x2KeyDegree s k ≠ 2) :
    x2InputBlock D s N k = x2GJ D s k * N k * (x2GJ D s k)ᵀ := by
  unfold x2InputBlock x2GJ
  simp only [if_neg hdeg, add_zero]

/-- For a degree-1 key whose columns pass `x2JColOK`, the input block is invariant under every site
permutation fixing its sorted type triple, for every source `N`. -/
theorem x2InputBlock_inv_of_ok (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (hok : x2JKeyOK s k = true)
    (hdeg : x2KeyDegree s k ≠ 2) (hsort : x2Sorted (x2KeyTypes s k)) (p : Fin 6)
    (hp : x2KeyTypes s k ∘ x2Perm3 p = x2KeyTypes s k) (a b : Fin 3 → ℕ) :
    x2Lookup (x2InputBlock x2DataConcrete s N k) (a ∘ x2Perm3 p) (b ∘ x2Perm3 p) =
      x2Lookup (x2InputBlock x2DataConcrete s N k) a b := by
  have hcols : ∀ c, c < x2KeySize s k → x2JColOK s k c = true := by
    intro c hc
    unfold x2JKeyOK at hok
    have hd : (x2KeyDegree s k == 2) = false := by
      cases h : (x2KeyDegree s k == 2)
      · rfl
      · exact absurd (beq_iff_eq.mp h) hdeg
    rw [hd, Bool.false_or] at hok
    exact List.all_eq_true.mp hok c (List.mem_range.mpr hc)
  rw [x2InputBlock_deg1 x2DataConcrete s N k hdeg]
  refine x2Lookup_stab_of_swaps _ (x2KeyTypes s k) hsort ?_ ?_ p hp a b
  · intro ht a b
    apply x2Lookup_conj_inv _ _ (x2Perm3 2) ((x2JSign s k : ℤ) : ℚ) (x2JSign_sq s k) _ a b
    intro a' c
    have hm : x2KeyMult s k 0 = x2KeyMult s k 1 := by
      show x2Mult s (x2KeyTypes s k 0) = x2Mult s (x2KeyTypes s k 1)
      rw [ht]
    exact x2GJ_swap01 x2DataConcrete s k _ ht
      (x2Image_swap01 s k (x2JSign s k) hm
        (fun y0 y1 y2 c' h0 h1 h2 hc' => x2JColOK_law01 s k c' (hcols c' hc') ht y0 y1 y2 h0 h1 h2))
      (a' 0) (a' 1) (a' 2) c
  · intro ht a b
    apply x2Lookup_conj_inv _ _ (x2Perm3 1) ((x2JSign s k : ℤ) : ℚ) (x2JSign_sq s k) _ a b
    intro a' c
    have hm : x2KeyMult s k 1 = x2KeyMult s k 2 := by
      show x2Mult s (x2KeyTypes s k 1) = x2Mult s (x2KeyTypes s k 2)
      rw [ht]
    exact x2GJ_swap12 x2DataConcrete s k _ ht
      (x2Image_swap12 s k (x2JSign s k) hm
        (fun y0 y1 y2 c' h0 h1 h2 hc' => x2JColOK_law12 s k c' (hcols c' hc') ht y0 y1 y2 h0 h1 h2))
      (a' 0) (a' 1) (a' 2) c

end X2
end ThreeCopyQutritWerner
