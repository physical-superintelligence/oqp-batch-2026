module

public import ThreeCopyQutritWerner.CertificateX2InputSite
public import ThreeCopyQutritWerner.CertificateX2InputBlocks
public import ThreeCopyQutritWerner.CertificateX2CoreLemmas

@[expose] public section


/-!
# Input stage: the factors `GJ` and `V = GJ F` as checked packed columns

For a source key with local types `(t₀, t₁, t₂)` and multiplicities `(m₀, m₁, m₂)`, an image column
`P` (11-bit slots, offset `2^10`, flat order `(z₀ m₁ + z₁) m₂ + z₂`) is re-packed at `W` bits
(`spreadW`) and contracted site by site with the local Gram matrices (`siteApply`, sites 2, 1, 0):
`gjApply` is the column of `GJ = (G ⊗ G ⊗ G) J`. `gjCheck` compares it with a candidate column, and
`gjCheck_sound` gives every slot of the candidate as the triple sum of `x2GJ_get3`. `vCheck` is one
natural linear combination `V_c = ∑_d F[d, c] GJ_d` with the factor's packed column digits as offset
scalars (80-bit slots, offset `2^79`).
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Signed parts of the local Gram entries -/

/-- Positive part of a local Gram entry. -/
def glp (s : Fin 3) (t : Fin 8) (x y : ℕ) : ℕ := (x2gl s t x y).toNat

/-- Negative part of a local Gram entry. -/
def gln (s : Fin 3) (t : Fin 8) (x y : ℕ) : ℕ := (-x2gl s t x y).toNat

theorem glp_sub_gln (s : Fin 3) (t : Fin 8) (x y : ℕ) :
    ((glp s t x y : ℕ) : ℤ) - (gln s t x y : ℤ) = x2gl s t x y := Int.toNat_sub_toNat_neg _

theorem glp_add_gln (s : Fin 3) (t : Fin 8) (x y : ℕ) :
    ((glp s t x y : ℕ) : ℤ) + (gln s t x y : ℤ) = |x2gl s t x y| := by
  unfold glp gln
  rw [← Int.natCast_add, Int.toNat_add_toNat_neg_eq_natAbs, Int.natCast_natAbs]

/-- Row absolute sums of a local Gram matrix, checked by the kernel against a bound. -/
noncomputable def glRowOK (s : Fin 3) (t : Fin 8) (m b : ℕ) : Bool :=
  (List.range m).all (fun x => Nat.ble (natSum m (fun y => glp s t x y + gln s t x y)) b)

theorem glRowOK_sound (s : Fin 3) (t : Fin 8) (m b : ℕ) (h : glRowOK s t m b = true) (x : ℕ) (hx : x < m) :
    ∑ y ∈ Finset.range m, (((glp s t x y : ℕ) : ℤ) + (gln s t x y : ℤ)) ≤ b := by
  unfold glRowOK at h
  have hx' := Nat.le_of_ble_eq_true (List.all_eq_true.mp h x (List.mem_range.mpr hx))
  rw [natSum_eq] at hx'
  have e : ∑ y ∈ Finset.range m, (((glp s t x y : ℕ) : ℤ) + (gln s t x y : ℤ)) =
      ((∑ y ∈ Finset.range m, (glp s t x y + gln s t x y) : ℕ) : ℤ) := by push_cast; rfl
  rw [e]
  exact_mod_cast hx'

/-! ### Bounds for site contractions -/

theorem siteVal_abs_le (W m B : ℕ) (gp gn : ℕ → ℕ → ℕ) (E a x b : ℕ) (M R : ℤ) (hM : 0 ≤ M)
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


theorem ent_abs_le (W E k : ℕ) (hW : 1 ≤ W) : |ent W (W - 1) E k| ≤ 2 ^ (W - 1) := by
  have h := ent_range W E k hW
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem site_decomp (m B k : ℕ) (hm : 1 ≤ m) (hB : 1 ≤ B) :
    k = (k / (m * B) * m + k / B % m) * B + k % B := by
  have e1 : k / (m * B) = k / B / m := by rw [Nat.mul_comm m B, Nat.div_div_eq_div_mul]
  have e2 := Nat.div_add_mod (k / B) m
  have e3 := Nat.div_add_mod k B
  rw [e1]
  calc k = B * (k / B) + k % B := e3.symm
    _ = B * (m * (k / B / m) + k / B % m) + k % B := by rw [e2]
    _ = (k / B / m * m + k / B % m) * B + k % B := by ring

/-- One site stage with its bounds: range, slot bounds and slot values. -/
theorem siteApply_bound (W A m B : ℕ) (gp gn : ℕ → ℕ → ℕ) (E M R : ℕ) (hW : 2 ≤ W) (hB : 1 ≤ B)
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
    exact siteVal_abs_le W m B gp gn E a x b M R (by positivity)
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
  rw [site_decomp m B k hm hB, hent _ ha _ hx _ hb]
  push_cast
  exact hval _ ha _ hx _ hb

/-! ### Image columns re-packed at `W` bits -/

/-- Re-packing of an 11-bit image column at `W` bits with offset `2^(W-1)`. -/
noncomputable def spreadW (W n P : ℕ) : ℕ := spreadDC 11 W 16 n P + (2 ^ (W - 1) - 2 ^ 10) * repunit W n

theorem spreadW_spec (W n P : ℕ) (hW : 12 ≤ W) :
    spreadW W n P < 2 ^ (W * n) ∧ ∀ t < n, ent W (W - 1) (spreadW W n P) t = ent 11 10 P t := by
  have hW1 : 1 ≤ W := by omega
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
  have hsum : spreadW W n P = ∑ t ∈ Finset.range n, (dig 11 P t + (2 ^ (W - 1) - 2 ^ 10)) * (2 ^ W) ^ t := by
    unfold spreadW
    rw [spreadDC_eq, repunit_eq W n hW1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [← pow_mul]
    ring
  constructor
  · rw [hsum, pow_mul]
    exact sum_digits_lt (2 ^ W) _ hcoef n
  · intro t ht
    have hd : dig W (spreadW W n P) t = dig 11 P t + (2 ^ (W - 1) - 2 ^ 10) := by
      rw [hsum]
      unfold dig
      rw [pow_mul 2 W t]
      exact sum_digit (2 ^ W) n _ (Nat.two_pow_pos W) hcoef t ht
    unfold ent
    rw [hd, Nat.cast_add, Nat.cast_sub hoff]
    push_cast
    ring

/-! ### The column of `GJ` -/

/-- The column of `GJ = (G ⊗ G ⊗ G) J` from an image column (sites 2, 1, 0). -/
noncomputable def gjApply (W : ℕ) (s : Fin 3) (t0 t1 t2 : Fin 8) (m0 m1 m2 P : ℕ) : ℕ :=
  siteApply W 1 m0 (m1 * m2) (glp s t0) (gln s t0)
    (siteApply W m0 m1 m2 (glp s t1) (gln s t1)
      (siteApply W (m0 * m1) m2 1 (glp s t2) (gln s t2) (spreadW W (m0 * m1 * m2) P)))

/-- A candidate `GJ` column equals the computed one. -/
noncomputable def gjCheck (W : ℕ) (s : Fin 3) (t0 t1 t2 : Fin 8) (m0 m1 m2 P Q : ℕ) : Bool :=
  Nat.beq (gjApply W s t0 t1 t2 m0 m1 m2 P) Q

theorem gjCheck_sound (W : ℕ) (s : Fin 3) (t0 t1 t2 : Fin 8) (m0 m1 m2 P Q : ℕ) (hW : 48 ≤ W)
    (h0 : 1 ≤ m0) (h1 : 1 ≤ m1) (h2 : 1 ≤ m2)
    (hr0 : glRowOK s t0 m0 512 = true) (hr1 : glRowOK s t1 m1 512 = true) (hr2 : glRowOK s t2 m2 512 = true)
    (hc : gjCheck W s t0 t1 t2 m0 m1 m2 P Q = true) :
    Q < 2 ^ (W * (m0 * m1 * m2)) ∧ (∀ k < m0 * m1 * m2, |ent W (W - 1) Q k| ≤ 2 ^ 37) ∧
      ∀ y0 < m0, ∀ y1 < m1, ∀ y2 < m2,
      ent W (W - 1) Q ((y0 * m1 + y1) * m2 + y2) =
        ∑ z0 ∈ Finset.range m0, ∑ z1 ∈ Finset.range m1, ∑ z2 ∈ Finset.range m2,
          x2gl s t0 y0 z0 * (x2gl s t1 y1 z1 * (x2gl s t2 y2 z2 * ent 11 10 P ((z0 * m1 + z1) * m2 + z2))) := by
  have hW2 : 2 ≤ W := by omega
  have hpw : ∀ e, e ≤ 37 → (2 : ℕ) ^ e < 2 ^ (W - 1) := fun e he =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hQ : gjApply W s t0 t1 t2 m0 m1 m2 P = Q := Nat.eq_of_beq_eq_true hc
  subst hQ
  unfold gjApply
  obtain ⟨hEl, hEe⟩ := spreadW_spec W (m0 * m1 * m2) P (by omega)
  -- stage 2 (B = 1)
  have hL2 : m0 * m1 * (m2 * 1) = m0 * m1 * m2 := by ring
  have hEb2 : ∀ k < m0 * m1 * (m2 * 1), |ent W (W - 1) (spreadW W (m0 * m1 * m2) P) k| ≤ 2 ^ 10 := by
    intro k hk
    rw [hL2] at hk
    rw [hEe k hk]
    have := ent_abs_le 11 P k (by norm_num)
    simpa using this
  obtain ⟨hS2l, hS2b, hS2e⟩ := siteApply_bound W (m0 * m1) m2 1 (glp s t2) (gln s t2)
    (spreadW W (m0 * m1 * m2) P) (2 ^ 10) 512 hW2 le_rfl h2 (by rw [hL2]; exact hEl) hEb2
    (glRowOK_sound s t2 m2 512 hr2) (by
      calc 512 * 2 ^ 10 = 2 ^ 19 := by norm_num
        _ < 2 ^ (W - 1) := hpw 19 (by norm_num))
  -- stage 1
  have hL1 : m0 * (m1 * m2) = m0 * m1 * (m2 * 1) := by ring
  obtain ⟨hS1l, hS1b, hS1e⟩ := siteApply_bound W m0 m1 m2 (glp s t1) (gln s t1) _ (512 * 2 ^ 10) 512 hW2 h2 h1
    (by rw [hL1]; exact hS2l) (by intro k hk; rw [hL1] at hk; exact hS2b k hk)
    (glRowOK_sound s t1 m1 512 hr1) (by
      calc 512 * (512 * 2 ^ 10) = 2 ^ 28 := by norm_num
        _ < 2 ^ (W - 1) := hpw 28 (by norm_num))
  -- stage 0
  have hL0 : 1 * (m0 * (m1 * m2)) = m0 * (m1 * m2) := by ring
  obtain ⟨hS0l, hS0b, hS0e⟩ := siteApply_bound W 1 m0 (m1 * m2) (glp s t0) (gln s t0) _
    (512 * (512 * 2 ^ 10)) 512 hW2 (Nat.mul_pos (by omega) (by omega)) h0
    (by rw [hL0]; exact hS1l) (by intro k hk; rw [hL0] at hk; exact hS1b k hk)
    (glRowOK_sound s t0 m0 512 hr0) (by
      calc 512 * (512 * (512 * 2 ^ 10)) = 2 ^ 37 := by norm_num
        _ < 2 ^ (W - 1) := hpw 37 (by norm_num))
  have hn : m0 * m1 * m2 = 1 * (m0 * (m1 * m2)) := by ring
  refine ⟨lt_of_lt_of_eq hS0l (by rw [hn]), ?_, ?_⟩
  · intro k hk
    rw [hn] at hk
    have h37 := hS0b k hk
    have e37 : ((512 * (512 * (512 * 2 ^ 10)) : ℕ) : ℤ) = 2 ^ 37 := by norm_num
    rw [e37] at h37
    exact h37
  · intro y0 hy0 y1 hy1 y2 hy2
    have i0 : (y0 * m1 + y1) * m2 + y2 = (0 * m0 + y0) * (m1 * m2) + (y1 * m2 + y2) := by ring
    have hb0 : y1 * m2 + y2 < m1 * m2 := by nlinarith
    rw [i0, hS0e 0 (by norm_num) y0 hy0 _ hb0]
    unfold siteVal
    apply Finset.sum_congr rfl
    intro z0 hz0
    have hz0' := Finset.mem_range.mp hz0
    have i1 : (0 * m0 + z0) * (m1 * m2) + (y1 * m2 + y2) = (z0 * m1 + y1) * m2 + y2 := by ring
    rw [i1, hS1e z0 hz0' y1 hy1 y2 hy2, glp_sub_gln]
    unfold siteVal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z1 hz1
    have hz1' := Finset.mem_range.mp hz1
    have i2 : (z0 * m1 + z1) * m2 + y2 = ((z0 * m1 + z1) * m2 + y2) * 1 + 0 := by ring
    have ha2 : z0 * m1 + z1 < m0 * m1 := by nlinarith
    rw [i2, hS2e (z0 * m1 + z1) ha2 y2 hy2 0 (by norm_num), glp_sub_gln]
    unfold siteVal
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z2 hz2
    have hz2' := Finset.mem_range.mp hz2
    have i3 : ((z0 * m1 + z1) * m2 + z2) * 1 + 0 = (z0 * m1 + z1) * m2 + z2 := by ring
    have hk3 : (z0 * m1 + z1) * m2 + z2 < m0 * m1 * m2 := by
      have := site_idx_lt m0 m1 m2 z0 z1 z2 hz0' hz1' hz2'
      rwa [← Nat.mul_assoc] at this
    rw [i3, hEe _ hk3, glp_sub_gln]

/-! ### The columns of `V = GJ F` -/

/-- Column `c` of `V = GJ F`: one natural linear combination of the `GJ` columns with the digits
of the factor column (80-bit slots, offset `2^79`) as offset scalars. -/
noncomputable def vCheck (W n r : ℕ) (GJcols : List ℕ) (Fcol Vcol : ℕ) : Bool :=
  natAxpyCheck W n 79 (digs 80 r Fcol) GJcols Vcol (natAxpyCorr W n 79 GJcols) &&
    slotBoundCheck W 90 n Vcol

theorem vCheck_sound (W n r : ℕ) (GJcols : List ℕ) (Fcol Vcol : ℕ) (hW : 160 ≤ W)
    (hlen : GJcols.length = r) (hr : r ≤ 512)
    (hGJ : ∀ d < r, GJcols.getD d 0 < 2 ^ (W * n) ∧ ∀ k < n, |ent W (W - 1) (GJcols.getD d 0) k| ≤ 2 ^ 37)
    (hc : vCheck W n r GJcols Fcol Vcol = true) :
    Vcol < 2 ^ (W * n) ∧ (∀ k < n, |ent W (W - 1) Vcol k| ≤ 2 ^ 90) ∧
      ∀ k < n, ent W (W - 1) Vcol k =
        ∑ d : Fin r, ent 80 79 Fcol d * ent W (W - 1) (GJcols.getD d 0) k := by
  unfold vCheck at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hax, hbd⟩ := hc
  obtain ⟨hlt, hbnd⟩ := slotBoundCheck_sound W 90 n Vcol (by omega) hbd
  have hsum : ∀ k, lincomb W (sScalars 79 (digs 80 r Fcol)) GJcols k =
      ∑ d : Fin r, ent 80 79 Fcol d * ent W (W - 1) (GJcols.getD d 0) k := by
    intro k
    rw [lincomb_getD W 79 r k _ _ (digs_length 80 r Fcol) hlen]
    apply Finset.sum_congr rfl
    intro d _
    rw [digs_getD 80 r Fcol d d.isLt]
    rfl
  have hmem : ∀ E ∈ GJcols, E < 2 ^ (W * n) := by
    intro E hE
    obtain ⟨d, hd, rfl⟩ := List.getElem_of_mem hE
    have := (hGJ d (by omega)).1
    rwa [List.getD_eq_getElem _ _ hd] at this
  have hlin : ∀ k < n, |lincomb W (sScalars 79 (digs 80 r Fcol)) GJcols k| < 2 ^ (W - 1) := by
    intro k hk
    rw [hsum]
    calc |∑ d : Fin r, ent 80 79 Fcol d * ent W (W - 1) (GJcols.getD d 0) k|
        ≤ ∑ d : Fin r, |ent 80 79 Fcol d * ent W (W - 1) (GJcols.getD d 0) k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d : Fin r, (2 ^ 79 * 2 ^ 37 : ℤ) := by
          apply Finset.sum_le_sum
          intro d _
          rw [abs_mul]
          have h1 := ent_abs_le 80 Fcol d (by norm_num)
          norm_num at h1
          exact mul_le_mul h1 ((hGJ d d.isLt).2 k hk) (abs_nonneg _) (by positivity)
      _ = (r : ℤ) * (2 ^ 79 * 2 ^ 37) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
      _ < 2 ^ (W - 1) := by
          have hr' : (r : ℤ) ≤ 2 ^ 9 := by exact_mod_cast (show r ≤ 2 ^ 9 by omega)
          have h2 : (2 : ℤ) ^ 9 * (2 ^ 79 * 2 ^ 37) < 2 ^ (W - 1) := by
            rw [← pow_add, ← pow_add]
            exact pow_lt_pow_right₀ (by norm_num) (by omega)
          nlinarith
  refine ⟨hlt, hbnd, ?_⟩
  intro k hk
  rw [← natAxpyCheck_sound W n 79 _ GJcols Vcol (by omega) (by rw [digs_length, hlen]) hmem hlin hax k hk, hsum]

end X2
end ThreeCopyQutritWerner
