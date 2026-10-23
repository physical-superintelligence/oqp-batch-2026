module

public import ThreeCopyQutritWerner.CertificateX2CoreLemmas

@[expose] public section


/-!
# Output stage: generic lemmas

The h-block output `Jᵀ X J` of a block matrix `X` (ambient `α`, `N` points) and an image `J`
(`r` columns, packed with 11-bit slots, offset `2^10`, in the flat order `f`), from

* `Xcols`: the columns of `X`, listed in the flat order of `y`, each packed over `x` in an order
  `e : α ≃ Fin N` of our choice (`W`-bit slots, offset `2^(W-1)`, scale `σ`);
* `Ycols`: `Y = X J` by columns (one natural linear-combination check per column: the image
  digits are the scalars, the columns of `X` the fibers);
* `Jrows`: the rows of `J` in the order `e` (`r` slots each);
* `Orows`: `Jᵀ Y` by columns (one check per column: the slots of `Y` are the scalars).

`x2BlockProj` states `Jᵀ X J = O / σ` entrywise. Run assembly of the columns of `X` from packed
tensor fibers: `runOf`, `dig_runOf`, `concatFibers_dig`.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-- The `m` slots of `F` starting at slot `off`. -/
def runOf (W m off F : ℕ) : ℕ := (F >>> (W * off)) &&& (2 ^ (W * m) - 1)

theorem runOf_lt (W m off F : ℕ) : runOf W m off F < 2 ^ (W * m) := by
  unfold runOf
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem dig_runOf (W m off F s : ℕ) (hs : s < m) : dig W (runOf W m off F) s = dig W F (off + s) := by
  unfold runOf dig
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hWs : W * m = W * s + W * (m - s) := by
    rw [← mul_add]
    congr 1
    omega
  rw [hWs, pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  · rw [Nat.div_div_eq_div_mul, ← pow_add, show W * off + W * s = W * (off + s) by ring]
  · exact pow_dvd_pow 2 (by
      have : 1 ≤ m - s := by omega
      calc W = W * 1 := by ring
        _ ≤ W * (m - s) := Nat.mul_le_mul_left W this)

/-- Signed slot of an offset-`(W-1)` packed natural from an image column (11-bit, offset `2^10`). -/
theorem digs_getD_ent (W n x a : ℕ) (ha : a < n) :
    (((digs W n x).getD a 0 : ℕ) : ℤ) - 2 ^ (W - 1) = ent W (W - 1) x a := by
  rw [digs_getD W n x a ha]
  rfl

/-- The output of an h-block from packed columns. -/
theorem x2BlockProj {α : Type*} [Fintype α] (W N r : ℕ) (e f : α ≃ Fin N)
    (Jcols Xcols Ycols Jrows Orows : List ℕ) (σ : ℚ) (Xb Yb : ℤ) (hW : 12 ≤ W)
    (hJc : Jcols.length = r) (hX : Xcols.length = N) (hY : Ycols.length = r)
    (hJr : Jrows.length = N) (hXlt : ∀ x ∈ Xcols, x < 2 ^ (W * N))
    (hJlt : ∀ x ∈ Jrows, x < 2 ^ (W * r))
    (hXb : ∀ i < N, ∀ k < N, |ent W (W - 1) (Xcols.getD i 0) k| ≤ Xb)
    (hJrow : ∀ (x : α) (c : ℕ), c < r →
      ent W (W - 1) (Jrows.getD (e x) 0) c = ent 11 10 (Jcols.getD c 0) (f x))
    (hJb : ∀ i < N, ∀ c < r, |ent W (W - 1) (Jrows.getD i 0) c| ≤ 2 ^ 10)
    (hb1 : (N : ℤ) * (2 ^ 10 * Xb) < 2 ^ (W - 1))
    (hYb : ∀ c < r, ∀ k < N, |ent W (W - 1) (Ycols.getD c 0) k| ≤ Yb)
    (hb2 : (N : ℤ) * (Yb * 2 ^ 10) < 2 ^ (W - 1)) (hYb0 : 0 ≤ Yb)
    (hYc : ∀ c < r, natAxpyCheck W N 10 (digs 11 N (Jcols.getD c 0)) Xcols (Ycols.getD c 0)
      (natAxpyCorr W N 10 Xcols) = true)
    (hOc : ∀ c < r, slotCheck W N r Jrows (Ycols.getD c 0) (Orows.getD c 0) = true)
    (c c' : Fin r) :
    ((Matrix.of fun (x : α) (c : Fin r) => (ent 11 10 (Jcols.getD c 0) (f x) : ℚ))ᵀ *
        (Matrix.of fun (x y : α) => (ent W (W - 1) (Xcols.getD (f y) 0) (e x) : ℚ) / σ) *
        (Matrix.of fun (x : α) (c : Fin r) => (ent 11 10 (Jcols.getD c 0) (f x) : ℚ))) c c' =
      (ent W (W - 1) (Orows.getD c' 0) c : ℚ) / σ := by
  -- Y = X J, column c'
  have hJdig : ∀ c < r, ∀ i < N, ent 11 10 (Jcols.getD c 0) i =
      (((digs 11 N (Jcols.getD c 0)).getD i 0 : ℕ) : ℤ) - 2 ^ 10 := by
    intro c _ i hi
    rw [digs_getD 11 N _ i hi]
    rfl
  have hJabs : ∀ c < r, ∀ i < N, |ent 11 10 (Jcols.getD c 0) i| ≤ 2 ^ 10 := by
    intro c _ i _
    have h0 : (0 : ℤ) ≤ (dig 11 (Jcols.getD c 0) i : ℤ) := by positivity
    have h1 : (dig 11 (Jcols.getD c 0) i : ℤ) < 2 ^ 11 := by
      exact_mod_cast Nat.mod_lt _ (by positivity)
    unfold ent
    rw [abs_le]
    constructor <;> linarith
  have hY : ∀ (c : ℕ), c < r → ∀ k < N,
      ∑ i : Fin N, ent 11 10 (Jcols.getD c 0) i * ent W (W - 1) (Xcols.getD i 0) k =
        ent W (W - 1) (Ycols.getD c 0) k := by
    intro c hc k hk
    have hs := natAxpyCheck_sound W N 10 (digs 11 N (Jcols.getD c 0)) Xcols (Ycols.getD c 0)
      (by omega) (by rw [digs_length, hX]) hXlt ?_ (hYc c hc) k hk
    · rw [lincomb_getD W 10 N k _ _ (digs_length 11 N _) hX] at hs
      rw [← hs]
      apply Finset.sum_congr rfl
      intro i _
      rw [hJdig c hc i i.isLt]
    · intro k' hk'
      rw [lincomb_getD W 10 N k' _ _ (digs_length 11 N _) hX]
      calc |∑ i : Fin N, (((digs 11 N (Jcols.getD c 0)).getD i 0 : ℤ) - 2 ^ 10) *
              ent W (W - 1) (Xcols.getD i 0) k'|
          ≤ ∑ i : Fin N, |(((digs 11 N (Jcols.getD c 0)).getD i 0 : ℤ) - 2 ^ 10) *
              ent W (W - 1) (Xcols.getD i 0) k'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, 2 ^ 10 * Xb := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul, ← hJdig c hc i i.isLt]
            exact mul_le_mul (hJabs c hc i i.isLt) (hXb i i.isLt k' hk') (abs_nonneg _)
              (by positivity)
        _ = (N : ℤ) * (2 ^ 10 * Xb) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < 2 ^ (W - 1) := hb1
  -- O = Jᵀ Y, column c'
  have hO : ∀ (c' : ℕ), c' < r → ∀ c < r,
      ∑ i : Fin N, ent W (W - 1) (Ycols.getD c' 0) i * ent W (W - 1) (Jrows.getD i 0) c =
        ent W (W - 1) (Orows.getD c' 0) c := by
    intro c' hc' c hc
    exact slotCheck_int W N r Jrows (Ycols.getD c' 0) (Orows.getD c' 0) (by omega) hJr hJlt
      (by
        intro k hk
        calc |∑ i : Fin N, ent W (W - 1) (Ycols.getD c' 0) i * ent W (W - 1) (Jrows.getD i 0) k|
            ≤ ∑ i : Fin N, |ent W (W - 1) (Ycols.getD c' 0) i * ent W (W - 1) (Jrows.getD i 0) k| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, Yb * 2 ^ 10 := by
              apply Finset.sum_le_sum
              intro i _
              rw [abs_mul]
              exact mul_le_mul (hYb c' hc' i i.isLt) (hJb i i.isLt k hk) (abs_nonneg _) hYb0
          _ = (N : ℤ) * (Yb * 2 ^ 10) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ < 2 ^ (W - 1) := hb2)
      (hOc c' hc') c hc
  -- assemble
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.mul_apply]
  have hinner : ∀ x : α, ∑ y : α, (ent W (W - 1) (Xcols.getD (f y) 0) (e x) : ℚ) / σ *
      (ent 11 10 (Jcols.getD c' 0) (f y) : ℚ) =
      (ent W (W - 1) (Ycols.getD c' 0) (e x) : ℚ) / σ := by
    intro x
    rw [← hY c' c'.isLt (e x) (e x).isLt, Int.cast_sum, Finset.sum_div]
    rw [← Equiv.sum_comp f.symm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Equiv.apply_symm_apply]
    push_cast
    ring
  simp_rw [hinner]
  rw [← hO c' c'.isLt c c.isLt, Int.cast_sum, Finset.sum_div]
  rw [← Equiv.sum_comp e.symm]
  apply Finset.sum_congr rfl
  intro i _
  have hj := hJrow (e.symm i) c c.isLt
  simp only [Equiv.apply_symm_apply] at hj ⊢
  rw [← hj]
  push_cast
  ring

end X2
end ThreeCopyQutritWerner

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Orders of a three-factor ambient -/

/-- Row-major order `(x₀, x₁, x₂)` (`x₂` fastest), the image packing order (`x2FlatIndex`). -/
def x2Flat3 (a b c : ℕ) : Fin a × Fin b × Fin c ≃ Fin (a * b * c) :=
  (Equiv.prodAssoc (Fin a) (Fin b) (Fin c)).symm.trans
    ((finProdFinEquiv.prodCongr (Equiv.refl (Fin c))).trans finProdFinEquiv)

theorem x2Flat3_val (a b c : ℕ) (x : Fin a × Fin b × Fin c) :
    (x2Flat3 a b c x : ℕ) = ((x.1 : ℕ) * b + x.2.1) * c + x.2.2 := by
  simp only [x2Flat3, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    finProdFinEquiv_apply_val, Equiv.prodAssoc_symm_apply, id]
  ring

/-- Order `(x₁, x₂, x₀)` (`x₀` fastest). -/
def x2Rot0 (a b c : ℕ) : Fin a × Fin b × Fin c ≃ Fin (a * b * c) :=
  ((Equiv.prodComm (Fin a) (Fin b × Fin c)).trans (Equiv.prodAssoc (Fin b) (Fin c) (Fin a))).trans
    ((x2Flat3 b c a).trans (finCongr (by ring)))

theorem x2Rot0_val (a b c : ℕ) (x : Fin a × Fin b × Fin c) :
    (x2Rot0 a b c x : ℕ) = ((x.2.1 : ℕ) * c + x.2.2) * a + x.1 := by
  simp only [x2Rot0, Equiv.trans_apply, finCongr_apply, Fin.val_cast, x2Flat3_val,
    Equiv.prodComm_apply, Prod.swap, Equiv.prodAssoc_apply]

/-- Order `(x₀, x₂, x₁)` (`x₁` fastest). -/
def x2Rot1 (a b c : ℕ) : Fin a × Fin b × Fin c ≃ Fin (a * b * c) :=
  ((Equiv.prodCongr (Equiv.refl (Fin a)) (Equiv.prodComm (Fin b) (Fin c)))).trans
    ((x2Flat3 a c b).trans (finCongr (by ring)))

theorem x2Rot1_val (a b c : ℕ) (x : Fin a × Fin b × Fin c) :
    (x2Rot1 a b c x : ℕ) = ((x.1 : ℕ) * c + x.2.2) * b + x.2.1 := by
  simp only [x2Rot1, Equiv.trans_apply, finCongr_apply, Fin.val_cast, x2Flat3_val,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id, Equiv.prodComm_apply, Prod.swap]

/-! ### Signed combination of two runs -/

/-- `r₁ + e r₂` for offset-`(W-1)` packed runs of `m` slots and `e ∈ {-1, 0, 1}`. -/
def runComb (W m : ℕ) (r₁ r₂ : ℕ) (e : ℤ) : ℕ :=
  if e = 0 then r₁ else if e = 1 then r₁ + r₂ - offset W (W - 1) m
  else r₁ + offset W (W - 1) m - r₂

/-- A natural below `2^(W m)` whose integer value is `offset + ∑ c_s 2^(W s)` with balanced `c` has
entries `c`. -/
theorem ent_of_balanced (W m R : ℕ) (c : ℕ → ℤ) (hW : 1 ≤ W)
    (hc : ∀ s < m, -(2 ^ (W - 1)) ≤ c s ∧ c s < 2 ^ (W - 1))
    (hR : (R : ℤ) = (∑ s ∈ Finset.range m, c s * 2 ^ (W * s)) + (offset W (W - 1) m : ℤ))
    (s : ℕ) (hs : s < m) : ent W (W - 1) R s = c s := by
  have hS := balanced_sum_cast W m hW c hc
  rw [hS] at hR
  have hRn : R = ∑ k ∈ Finset.range m,
      (if k < m then (c k + 2 ^ (W - 1)).toNat else 0) * (2 ^ W) ^ k := by exact_mod_cast hR
  have hfc : ∀ k, (if k < m then (c k + 2 ^ (W - 1)).toNat else 0) < 2 ^ W := by
    intro k
    split_ifs with hk
    · exact (toNat_digit_lt W hW (c k) (hc k hk)).1
    · positivity
  have hd := sum_digit (2 ^ W) m _ (by positivity) hfc s hs
  simp only [if_pos hs] at hd
  have hdig : dig W R s = (c s + 2 ^ (W - 1)).toNat := by
    unfold dig
    rw [hRn, pow_mul]
    exact hd
  unfold ent
  rw [hdig, (toNat_digit_lt W hW (c s) (hc s hs)).2]
  ring

/-- Entries of a signed combination of two runs. -/
theorem runComb_ent (W m r₁ r₂ : ℕ) (e : ℤ) (hW : 2 ≤ W) (he : e = 0 ∨ e = 1 ∨ e = -1)
    (h1 : r₁ < 2 ^ (W * m)) (h2 : r₂ < 2 ^ (W * m))
    (hb : ∀ s < m, |ent W (W - 1) r₁ s + e * ent W (W - 1) r₂ s| < 2 ^ (W - 1)) (s : ℕ) (hs : s < m) :
    ent W (W - 1) (runComb W m r₁ r₂ e) s = ent W (W - 1) r₁ s + e * ent W (W - 1) r₂ s := by
  have hW1 : 1 ≤ W := by omega
  have e1 := ent_expansion W (W - 1) m r₁ hW1 h1
  have e2 := ent_expansion W (W - 1) m r₂ hW1 h2
  have hc : ∀ k < m, -(2 ^ (W - 1)) ≤ ent W (W - 1) r₁ k + e * ent W (W - 1) r₂ k ∧
      ent W (W - 1) r₁ k + e * ent W (W - 1) r₂ k < 2 ^ (W - 1) := by
    intro k hk
    have := abs_lt.mp (hb k hk)
    constructor <;> linarith [this.1, this.2]
  have hsum : ∑ k ∈ Finset.range m, (ent W (W - 1) r₁ k + e * ent W (W - 1) r₂ k) * 2 ^ (W * k) =
      (∑ k ∈ Finset.range m, ent W (W - 1) r₁ k * 2 ^ (W * k)) +
        e * ∑ k ∈ Finset.range m, ent W (W - 1) r₂ k * 2 ^ (W * k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpos := balanced_sum_cast W m hW1 _ hc
  have hnn : (0 : ℤ) ≤ (∑ k ∈ Finset.range m,
      (ent W (W - 1) r₁ k + e * ent W (W - 1) r₂ k) * 2 ^ (W * k)) + (offset W (W - 1) m : ℤ) := by
    rw [hpos]
    positivity
  apply ent_of_balanced W m _ _ hW1 hc _ s hs
  unfold runComb
  rcases he with rfl | rfl | rfl
  · rw [if_pos rfl, hsum, ← e1]
    ring
  · rw [if_neg (by norm_num : (1 : ℤ) ≠ 0), if_pos rfl]
    have hle : offset W (W - 1) m ≤ r₁ + r₂ := by
      have : ((offset W (W - 1) m : ℕ) : ℤ) ≤ ((r₁ + r₂ : ℕ) : ℤ) := by
        push_cast
        linarith [hnn, hsum, e1, e2]
      exact_mod_cast this
    rw [Nat.cast_sub hle, hsum, ← e1, ← e2]
    push_cast
    ring
  · rw [if_neg (by norm_num : (-1 : ℤ) ≠ 0), if_neg (by norm_num : (-1 : ℤ) ≠ 1)]
    have hle : r₂ ≤ r₁ + offset W (W - 1) m := by
      have : ((r₂ : ℕ) : ℤ) ≤ ((r₁ + offset W (W - 1) m : ℕ) : ℤ) := by
        push_cast
        linarith [hnn, hsum, e1, e2]
      exact_mod_cast this
    rw [Nat.cast_sub hle, hsum, ← e1, ← e2]
    push_cast
    ring

/-- Slot `q m + s` of a column assembled from runs of `m` slots. -/
theorem ent_concat_runs (W m : ℕ) (runs : List ℕ) (hlt : ∀ r ∈ runs, r < 2 ^ (W * m)) (q s : ℕ)
    (hq : q < runs.length) (hs : s < m) :
    ent W (W - 1) (concatFibers W m runs) (q * m + s) = ent W (W - 1) (runs.getD q 0) s := by
  unfold ent
  rw [concatFibers_dig W m runs hlt q s hq hs]

end X2
end ThreeCopyQutritWerner
