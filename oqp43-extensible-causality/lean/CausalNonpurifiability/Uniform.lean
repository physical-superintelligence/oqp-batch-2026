module

public import CausalNonpurifiability.Certificates.Qubit

@[expose] public section


/-!
# `CausalNonpurifiability.Uniform`

Uniform (all-dimension) rank statement of `thm:main` (i): for every `m, d, n, e ≥ 2`,
`rank W_0 = 4de`.

Method. `W_0` is supported on `Π = P_m ⊗ I_d ⊗ P_n ⊗ I_e` (`Pi_mul_W0 : Π W_0 = W_0`), and on its
support it is invertible: each of the eight `2×2` blocks of `eq:positive-blocks` has determinant
`523, 763, 3, 83` (times `1/6400`), so the block-adjugate construction `Rinv` satisfies
`W_0 · Rinv = Π` (`W0_mul_Rinv`). Hence `rank W_0 = rank Π` (`Matrix.rank_mul_le_left` both
ways), and `Π` is a `0/1` diagonal matrix with exactly `2·d·2·e = 4de` ones
(`Matrix.rank_diagonal`). At four qubit ports this gives `rank W_q = 16` (`eq:qubit-minimum`),
also obtained directly from positive definiteness (`wq_rank`).

Manuscript anchors: `thm:main` (i), `eq:positive-blocks`, `eq:qubit-minimum`.
-/

set_option autoImplicit false

namespace CausalNonpurifiability

open Matrix
open scoped Kronecker ComplexOrder

section LocalUnits
variable {r : ℕ}

lemma proj_mul_self (r k : ℕ) : proj r k * proj r k = proj r k := by
  rw [proj_eq, diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> norm_num

lemma proj_mul_proj_of_ne (r : ℕ) {k l : ℕ} (h : k ≠ l) : proj r k * proj r l = 0 := by
  rw [proj_eq, proj_eq, diagonal_mul_diagonal]
  ext i j
  simp only [diagonal_apply, Matrix.zero_apply]
  split_ifs <;> first | omega | norm_num

lemma Pplus_mul_Pplus : Pplus r * Pplus r = Pplus r := by
  rw [Pplus_eq, diagonal_mul_diagonal]; congr 1; funext i; split_ifs <;> norm_num

lemma Pplus_mul_proj_one : Pplus r * proj r 1 = 0 := by
  rw [Pplus_eq, proj_eq, diagonal_mul_diagonal]
  ext i j
  simp only [diagonal_apply, Matrix.zero_apply]
  split_ifs <;> first | omega | norm_num

lemma proj_one_mul_Pplus : proj r 1 * Pplus r = 0 := by
  rw [Pplus_eq, proj_eq, diagonal_mul_diagonal]
  ext i j
  simp only [diagonal_apply, Matrix.zero_apply]
  split_ifs <;> first | omega | norm_num

lemma proj_zero_mul_X : proj r 0 * X r = unit r 0 1 := by
  ext i j
  rw [proj_eq, diagonal_mul]
  simp only [X_apply, unit, of_apply]
  split_ifs <;> first | omega | norm_num

lemma proj_one_mul_X : proj r 1 * X r = unit r 1 0 := by
  ext i j
  rw [proj_eq, diagonal_mul]
  simp only [X_apply, unit, of_apply]
  split_ifs <;> first | omega | norm_num

lemma X_mul_proj_zero : X r * proj r 0 = unit r 1 0 := by
  ext i j
  rw [proj_eq, mul_diagonal]
  simp only [X_apply, unit, of_apply]
  split_ifs <;> first | omega | norm_num

lemma X_mul_proj_one : X r * proj r 1 = unit r 0 1 := by
  ext i j
  rw [proj_eq, mul_diagonal]
  simp only [X_apply, unit, of_apply]
  split_ifs <;> first | omega | norm_num

lemma P_mul_theta : P r * theta r = theta r := by
  rw [P_eq, theta_eq, diagonal_mul_diagonal]; congr 1; funext i
  split_ifs <;> first | omega | norm_num

end LocalUnits

section Kron4Zero
variable {m d n e : ℕ}

lemma kron4_zero₁ (B : Matrix (Fin d) (Fin d) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (D : Matrix (Fin e) (Fin e) ℚ) : kron4 (0 : Matrix (Fin m) (Fin m) ℚ) B C D = 0 := by
  ext x y; simp [kron4_apply]

lemma kron4_zero₂ (A : Matrix (Fin m) (Fin m) ℚ) (C : Matrix (Fin n) (Fin n) ℚ)
    (D : Matrix (Fin e) (Fin e) ℚ) : kron4 A (0 : Matrix (Fin d) (Fin d) ℚ) C D = 0 := by
  ext x y; simp [kron4_apply]

lemma kron4_zero₄ (A : Matrix (Fin m) (Fin m) ℚ) (B : Matrix (Fin d) (Fin d) ℚ)
    (C : Matrix (Fin n) (Fin n) ℚ) : kron4 A B C (0 : Matrix (Fin e) (Fin e) ℚ) = 0 := by
  ext x y; simp [kron4_apply]

end Kron4Zero

/-! ### The supported inverse (`eq:positive-blocks`, determinants `523, 763, 3, 83`) -/

section Inverse
variable {m d n e : ℕ}

/-- `blk x y s · blk y x (-s) = (xy - s²) P_n`: the `2×2` adjugate identity, padded. -/
lemma blk_mul_blk_adj (hn : 2 ≤ n) (x y s : ℚ) :
    blk n x y s * blk n y x (-s) = (x * y - s ^ 2) • P n := by
  simp only [blk, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, proj_mul_self,
    proj_mul_proj_of_ne n Nat.zero_ne_one, proj_mul_proj_of_ne n Nat.one_ne_zero,
    proj_zero_mul_X, proj_one_mul_X, X_mul_proj_zero, X_mul_proj_one, X_mul_X hn, smul_zero,
    add_zero, zero_add, P]
  module

/-- Supported inverse of the block `wblk θa za σ τ`: the scaled adjugate
`(1/det) · blk y x (-s)`, `det = xy - s²`. -/
def winv (n : ℕ) (θa za σ τ : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (1 / ((θa * (3 / 4) + σ / 20) * (θa * (1 / 4) - σ / 20) - (za * τ / 20) ^ 2)) •
    blk n (θa * (1 / 4) - σ / 20) (θa * (3 / 4) + σ / 20) (-(za * τ / 20))

lemma wblk_mul_winv (hn : 2 ≤ n) (θa za σ τ : ℚ)
    (hD : (θa * (3 / 4) + σ / 20) * (θa * (1 / 4) - σ / 20) - (za * τ / 20) ^ 2 ≠ 0) :
    wblk n θa za σ τ * winv n θa za σ τ = P n := by
  rw [wblk_eq_blk, winv, Matrix.mul_smul, blk_mul_blk_adj hn, smul_smul, one_div_mul_cancel hD,
    one_smul]

/-- The supported inverse of `W_0`: block adjugates on the eight blocks of `eq:positive-blocks`
(determinants `523/6400, 763/6400, 3/6400, 83/6400`), zero on `Π^⊥`. -/
def Rinv (m d n e : ℕ) : Matrix (Lab m d n e) (Lab m d n e) ℚ :=
  kron4 (proj m 0) (Pplus d) (winv n (3 / 4) 1 1 1) (Pplus e)
    + kron4 (proj m 0) (Pplus d) (winv n (3 / 4) 1 1 (-1)) (proj e 1)
    + kron4 (proj m 0) (proj d 1) (winv n (3 / 4) 1 (-1) 1) (Pplus e)
    + kron4 (proj m 0) (proj d 1) (winv n (3 / 4) 1 (-1) (-1)) (proj e 1)
    + kron4 (proj m 1) (Pplus d) (winv n (1 / 4) (-1) 1 1) (Pplus e)
    + kron4 (proj m 1) (Pplus d) (winv n (1 / 4) (-1) 1 (-1)) (proj e 1)
    + kron4 (proj m 1) (proj d 1) (winv n (1 / 4) (-1) (-1) 1) (Pplus e)
    + kron4 (proj m 1) (proj d 1) (winv n (1 / 4) (-1) (-1) (-1)) (proj e 1)

/-- Determinants of the four block types, in units of `1/6400`: `523, 763, 3, 83`. -/
theorem positive_blocks_determinants_scaled : ((3 / 4 : ℚ) * (3 / 4) + 1 / 20) * (3 / 4 * (1 / 4) - 1 / 20) - (1 * 1 / 20) ^ 2 = 523 / 6400
    ∧ ((3 / 4 : ℚ) * (3 / 4) + -1 / 20) * (3 / 4 * (1 / 4) - -1 / 20) - (1 * 1 / 20) ^ 2 = 763 / 6400
    ∧ ((1 / 4 : ℚ) * (3 / 4) + 1 / 20) * (1 / 4 * (1 / 4) - 1 / 20) - (-1 * 1 / 20) ^ 2 = 3 / 6400
    ∧ ((1 / 4 : ℚ) * (3 / 4) + -1 / 20) * (1 / 4 * (1 / 4) - -1 / 20) - (-1 * 1 / 20) ^ 2 = 83 / 6400 := by
  norm_num

/-- `W_0 · Rinv = Π`. -/
theorem W0_mul_Rinv (hn : 2 ≤ n) : W0 m d n e * Rinv m d n e = Pi m d n e := by
  have h1 := wblk_mul_winv hn (3 / 4) 1 1 1 (by norm_num)
  have h2 := wblk_mul_winv hn (3 / 4) 1 1 (-1) (by norm_num)
  have h3 := wblk_mul_winv hn (3 / 4) 1 (-1) 1 (by norm_num)
  have h4 := wblk_mul_winv hn (3 / 4) 1 (-1) (-1) (by norm_num)
  have h5 := wblk_mul_winv hn (1 / 4) (-1) 1 1 (by norm_num)
  have h6 := wblk_mul_winv hn (1 / 4) (-1) 1 (-1) (by norm_num)
  have h7 := wblk_mul_winv hn (1 / 4) (-1) (-1) 1 (by norm_num)
  have h8 := wblk_mul_winv hn (1 / 4) (-1) (-1) (-1) (by norm_num)
  rw [W0_eq_blocks, Rinv]
  simp only [Matrix.add_mul, Matrix.mul_add, kron4_mul_kron4, proj_mul_self,
    proj_mul_proj_of_ne _ Nat.zero_ne_one, proj_mul_proj_of_ne _ Nat.one_ne_zero, Pplus_mul_Pplus,
    Pplus_mul_proj_one, proj_one_mul_Pplus, kron4_zero₁, kron4_zero₂, kron4_zero₄, add_zero,
    zero_add, h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [Pi, kron4_P₁_split, kron4_one₂_split, kron4_one₄_split]
  abel

/-- `Π · W_0 = W_0`: `W_0` is supported on `Π`. -/
theorem Pi_mul_W0 : Pi m d n e * W0 m d n e = W0 m d n e := by
  rw [W0, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_add, Pi_mul_GA, Pi_mul_GB, Qtheta_eq_kron4,
    Pi, kron4_mul_kron4, P_mul_theta, P_mul_theta, Matrix.one_mul, Matrix.one_mul]

/-- **Supported inverse witness**: `W_0 · Rinv = Π ∧ Π · W_0 = W_0`. -/
theorem supported_inverse (hn : 2 ≤ n) :
    W0 m d n e * Rinv m d n e = Pi m d n e ∧ Pi m d n e * W0 m d n e = W0 m d n e :=
  ⟨W0_mul_Rinv hn, Pi_mul_W0⟩

end Inverse

/-! ### Rank of `Π` and of `W_0` -/

section Rank
variable {m d n e : ℕ}

/-- Diagonal of `Π`: the indicator of `a, b ∈ {0, 1}`. -/
def wPi (m d n e : ℕ) : Lab m d n e → ℚ :=
  fun x => (if x.1.1.val < 2 then 1 else 0) * (if x.2.1.val < 2 then 1 else 0)

lemma Pi_eq_diagonal : Pi m d n e = diagonal (wPi m d n e) := by
  ext ⟨⟨a, o⟩, ⟨b, t⟩⟩ ⟨⟨a', o'⟩, ⟨b', t'⟩⟩
  simp only [Pi, kron4_apply, P_eq, wPi, diagonal_apply, one_apply, Prod.mk.injEq]
  split_ifs <;> first | omega | norm_num

lemma card_filter_lt_two {r : ℕ} (hr : 2 ≤ r) :
    (Finset.univ.filter fun a : Fin r => a.val < 2).card = 2 := by
  have h : (Finset.univ.filter fun a : Fin r => a.val < 2) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    constructor <;> intro h <;> omega
  rw [h, Finset.card_pair]
  simp [Fin.ext_iff]

lemma filter_fst_lt_two {r q : ℕ} :
    ((Finset.univ : Finset (Fin r × Fin q)).filter fun y => y.1.val < 2)
      = (Finset.univ.filter fun a : Fin r => a.val < 2) ×ˢ Finset.univ := by
  ext ⟨a, o⟩
  simp

lemma wPi_ne_zero_iff (x : Lab m d n e) :
    ((wPi m d n e x : ℚ) : ℂ) ≠ 0 ↔ (x.1.1.val < 2 ∧ x.2.1.val < 2) := by
  by_cases h1 : x.1.1.val < 2 <;> by_cases h2 : x.2.1.val < 2 <;> simp [wPi, h1, h2]

/-- `rank Π = 4de`: `Π` is a `0/1` diagonal with `2·d·2·e` ones. -/
theorem rank_toC_Pi (hm : 2 ≤ m) (hn : 2 ≤ n) : (toC (Pi m d n e)).rank = 4 * d * e := by
  rw [Pi_eq_diagonal, toC_diagonal, rank_diagonal,
    Fintype.card_congr (Equiv.subtypeEquivRight (wPi_ne_zero_iff (m := m) (d := d) (n := n) (e := e))),
    Fintype.card_subtype, ← Finset.univ_product_univ,
    Finset.filter_product (fun y : Fin m × Fin d => y.1.val < 2) (fun z : Fin n × Fin e => z.1.val < 2),
    filter_fst_lt_two, filter_fst_lt_two, Finset.card_product, Finset.card_product,
    Finset.card_product, card_filter_lt_two hm, card_filter_lt_two hn, Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  ring

/-- `rank W_0 = rank Π` via the supported inverse. -/
theorem rank_W0_eq_rank_Pi (hn : 2 ≤ n) : (toC (W0 m d n e)).rank = (toC (Pi m d n e)).rank := by
  apply le_antisymm
  · calc (toC (W0 m d n e)).rank = (toC (Pi m d n e) * toC (W0 m d n e)).rank := by
          rw [← Matrix.map_mul, Pi_mul_W0]
      _ ≤ (toC (Pi m d n e)).rank := rank_mul_le_left _ _
  · calc (toC (Pi m d n e)).rank = (toC (W0 m d n e) * toC (Rinv m d n e)).rank := by
          rw [← Matrix.map_mul, W0_mul_Rinv hn]
      _ ≤ (toC (W0 m d n e)).rank := rank_mul_le_left _ _

/-- **Uniform rank** (`thm:main` (i)): `rank W_0 = 4de` for all `m, d, n, e ≥ 2`. -/
theorem uniform_rank (hm : 2 ≤ m) (hd : 2 ≤ d) (hn : 2 ≤ n) (he : 2 ≤ e) :
    (toC (W0 m d n e)).rank = 4 * d * e := by
  have _ := hd; have _ := he
  rw [rank_W0_eq_rank_Pi hn, rank_toC_Pi hm hn]

/-- `rank W_q = 16` from positive definiteness (`eq:qubit-minimum`). -/
theorem wq_rank : (toC WqEntries).rank = 16 := by
  rw [rank_of_isUnit _ wq_posDef.isUnit, Fintype.card_fin]

/-- `rank W_0 = 16` at four qubit ports, from the uniform statement. -/
theorem w0_qubit_rank : (toC (W0 2 2 2 2)).rank = 16 :=
  uniform_rank le_rfl le_rfl le_rfl le_rfl

end Rank

end CausalNonpurifiability
