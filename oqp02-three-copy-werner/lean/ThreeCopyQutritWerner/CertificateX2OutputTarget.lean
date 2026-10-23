module

public import ThreeCopyQutritWerner.CertificateX2OutputBlock

@[expose] public section


/-!
# Output stage: the target `x2Target D b` of an h block

`x2Target D b = Jᵀ (T₀ ⊗ T₁ ⊗ T₂) J` with the local targets `Tₜ = G_t - D_t / 2`. With `M_t = 2 G_t - D_t` (integers,
`|M_t| ≤ 62`), `8 x2Target = Jᵀ (M₀ ⊗ M₁ ⊗ M₂) J`. The columns of `M₀ ⊗ M₁ ⊗ M₂` (order `x2Flat3`) are assembled from
pieces `M₀[x₀,y₀] M₁[x₁,y₁] · M₂[·,y₂]` (a scaled packed run over `x₂`), and `x2PartProj` projects them.
`x2Target_eq_of_check`: `x2Target D b = x2TgtNum ⋯ / 8`, the numerators computed by the kernel.
-/

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Scaled runs and packed small columns -/

/-- `c` times an offset-encoded run of `m` slots, offset-encoded again. -/
def scaleRun (W m : ℕ) (c : ℤ) (R : ℕ) : ℕ :=
  if 0 ≤ c then c.toNat * R + offset W (W - 1) m - c.toNat * offset W (W - 1) m
  else (c.natAbs + 1) * offset W (W - 1) m - c.natAbs * R

theorem scaleRun_ent (W m : ℕ) (c : ℤ) (R : ℕ) (hW : 1 ≤ W) (hR : R < 2 ^ (W * m))
    (hb : ∀ s < m, |c * ent W (W - 1) R s| < 2 ^ (W - 1)) (s : ℕ) (hs : s < m) :
    ent W (W - 1) (scaleRun W m c R) s = c * ent W (W - 1) R s := by
  have e := ent_expansion W (W - 1) m R hW hR
  have hc : ∀ k < m, -(2 ^ (W - 1)) ≤ c * ent W (W - 1) R k ∧ c * ent W (W - 1) R k < 2 ^ (W - 1) := by
    intro k hk
    have := abs_lt.mp (hb k hk)
    constructor <;> linarith [this.1, this.2]
  have hsum : ∑ k ∈ Finset.range m, c * ent W (W - 1) R k * 2 ^ (W * k) =
      c * ((R : ℤ) - (offset W (W - 1) m : ℤ)) := by
    rw [e, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hpos := balanced_sum_cast W m hW (fun k => c * ent W (W - 1) R k) hc
  have hnn : (0 : ℤ) ≤ c * ((R : ℤ) - (offset W (W - 1) m : ℤ)) + (offset W (W - 1) m : ℤ) := by
    rw [← hsum, hpos]
    positivity
  have hR' : ((scaleRun W m c R : ℕ) : ℤ) =
      (∑ k ∈ Finset.range m, c * ent W (W - 1) R k * 2 ^ (W * k)) + (offset W (W - 1) m : ℤ) := by
    rw [hsum]
    unfold scaleRun
    split_ifs with h0
    · have hct : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg h0
      have hle : c.toNat * offset W (W - 1) m ≤ c.toNat * R + offset W (W - 1) m := by
        have : ((c.toNat * offset W (W - 1) m : ℕ) : ℤ) ≤ ((c.toNat * R + offset W (W - 1) m : ℕ) : ℤ) := by
          push_cast
          rw [hct]
          nlinarith [hnn]
        exact_mod_cast this
      rw [Nat.cast_sub hle]
      push_cast
      rw [hct]
      ring
    · have hneg : c < 0 := lt_of_not_ge h0
      have hle : c.natAbs * R ≤ (c.natAbs + 1) * offset W (W - 1) m := by
        have : ((c.natAbs * R : ℕ) : ℤ) ≤ (((c.natAbs + 1) * offset W (W - 1) m : ℕ) : ℤ) := by
          push_cast
          rw [abs_of_neg hneg]
          nlinarith [hnn]
        exact_mod_cast this
      rw [Nat.cast_sub hle]
      push_cast
      rw [abs_of_neg hneg]
      ring
  exact ent_of_balanced W m _ (fun k => c * ent W (W - 1) R k) hW hc hR' s hs

/-- A packed column of `m` small signed values (`W`-bit slots, offset `2^(W-1)`). -/
def packCol (W m : ℕ) (v : ℕ → ℤ) : ℕ :=
  concatFibers W 1 ((List.range m).map fun i => (v i + 2 ^ (W - 1)).toNat)

theorem packCol_lt (W m : ℕ) (v : ℕ → ℤ) (hW : 1 ≤ W)
    (hv : ∀ i < m, -(2 ^ (W - 1)) ≤ v i ∧ v i < 2 ^ (W - 1)) : packCol W m v < 2 ^ (W * m) := by
  unfold packCol
  have h := concatFibers_lt W 1 _ (x2o_mem_map_range m (fun i => (v i + 2 ^ (W - 1)).toNat)
    (fun f => f < 2 ^ (W * 1)) (fun i hi => by rw [mul_one]; exact (toNat_digit_lt W hW _ (hv i hi)).1))
  rw [List.length_map, List.length_range, mul_one] at h
  exact h

theorem packCol_ent (W m : ℕ) (v : ℕ → ℤ) (hW : 1 ≤ W)
    (hv : ∀ i < m, -(2 ^ (W - 1)) ≤ v i ∧ v i < 2 ^ (W - 1)) (i : ℕ) (hi : i < m) :
    ent W (W - 1) (packCol W m v) i = v i := by
  unfold packCol
  have hlt := x2o_mem_map_range m (fun i => (v i + 2 ^ (W - 1)).toNat) (fun f => f < 2 ^ (W * 1))
    (fun i hi => by rw [mul_one]; exact (toNat_digit_lt W hW _ (hv i hi)).1)
  have h := ent_concat_runs W 1 _ hlt i 0 (by simpa using hi) (by norm_num)
  rw [mul_one, add_zero] at h
  rw [h, x2o_getD_map_range m i _ hi]
  have hd := toNat_digit_lt W hW _ (hv i hi)
  unfold ent
  rw [x2o_dig_zero, Nat.mod_eq_of_lt hd.1, hd.2]
  ring

/-! ### The local target matrices -/

/-- `M_t = 2 G_t - D_t` (twice the local target), on natural indices. -/
def x2TgtM (t : Fin 8) (a b : ℕ) : ℤ :=
  2 * ((x2GramRows 0 t).getD a []).getD b 0 - ((x2SwapRows t).getD a []).getD b 0

/-- Entries of `M_t` are at most `2^6` in absolute value (`max = 62`). -/
theorem x2TgtM_bound : ∀ t : Fin 8, ∀ a < x2Mult 0 t, ∀ b < x2Mult 0 t, |x2TgtM t a b| ≤ 2 ^ 6 := by
  decide +kernel

theorem x2LocalTarget_apply (t : Fin 8) (i j : Fin (x2Mult 0 t)) :
    x2LocalTarget t i j = (x2TgtM t i j : ℚ) / 2 := by
  simp only [x2LocalTarget, x2Gram, x2SwapDiagram, x2TgtM, Matrix.sub_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- Piece `q = x₀ m₁ + x₁` of column `y` of `M₀ ⊗ M₁ ⊗ M₂`: a scaled run over `x₂`. -/
def x2TgtPiece (W : ℕ) (t0 t1 t2 : Fin 8) (y0 y1 y2 q : ℕ) : ℕ :=
  scaleRun W (x2Mult 0 t2) (x2TgtM t0 (q / x2Mult 0 t1) y0 * x2TgtM t1 (q % x2Mult 0 t1) y1)
    (packCol W (x2Mult 0 t2) (fun x2 => x2TgtM t2 x2 y2))

def x2TgtCol (W d : ℕ) (t0 t1 t2 : Fin 8) (y0 y1 y2 : ℕ) : ℕ :=
  colOfPieces W (x2Mult 0 t2) d (x2Mult 0 t0 * x2Mult 0 t1) (x2TgtPiece W t0 t1 t2 y0 y1 y2)

/-- Column list of `M₀ ⊗ M₁ ⊗ M₂` for block `b` (flat order of `y`, slots in flat order of `x`). -/
def x2TgtCols (W d : ℕ) (b : x2Key 0) : List ℕ :=
  x2Cols (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)
    (x2TgtCol W d (x2KeyTypes 0 b 0) (x2KeyTypes 0 b 1) (x2KeyTypes 0 b 2))

/-- Target numerators of block `b` (over `8`), computed by the kernel. -/
noncomputable def x2TgtNum (W d : ℕ) (b : x2Key 0) (Jcols : List ℕ) (c c' : ℕ) : ℤ :=
  ent W (W - 1) ((x2ORows W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b) Jcols
    (x2TgtCols W d b)
    (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols (fun i => i))).getD c' 0) c

theorem x2TgtM_range (W : ℕ) (hW : 8 ≤ W) (t : Fin 8) (a b : ℕ) (ha : a < x2Mult 0 t) (hb : b < x2Mult 0 t) :
    -(2 ^ (W - 1)) ≤ x2TgtM t a b ∧ x2TgtM t a b < 2 ^ (W - 1) := by
  have h := abs_le.mp (x2TgtM_bound t a ha b hb)
  have h6 : (2 : ℤ) ^ 6 < 2 ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  constructor <;> linarith [h.1, h.2]

theorem x2TgtCol_ent (W d : ℕ) (t0 t1 t2 : Fin 8) (hW : 20 ≤ W) (x0 x1 x2 y0 y1 y2 : ℕ)
    (hx0 : x0 < x2Mult 0 t0) (hx1 : x1 < x2Mult 0 t1) (hx2 : x2 < x2Mult 0 t2)
    (hy0 : y0 < x2Mult 0 t0) (hy1 : y1 < x2Mult 0 t1) (hy2 : y2 < x2Mult 0 t2) :
    ent W (W - 1) (x2TgtCol W d t0 t1 t2 y0 y1 y2) ((x0 * x2Mult 0 t1 + x1) * x2Mult 0 t2 + x2) =
      x2TgtM t0 x0 y0 * x2TgtM t1 x1 y1 * x2TgtM t2 x2 y2 := by
  have hW1 : 1 ≤ W := by omega
  have hq : x0 * x2Mult 0 t1 + x1 < x2Mult 0 t0 * x2Mult 0 t1 := x2o_lt_mul x0 x1 _ _ hx0 hx1
  unfold x2TgtCol
  rw [colOfPieces_ent W _ d _ _ _ x2 hq hx2]
  unfold x2TgtPiece
  obtain ⟨hd, hm⟩ := x2o_divmod x0 x1 (x2Mult 0 t1) hx1
  rw [hd, hm]
  have hv : ∀ i < x2Mult 0 t2, -(2 ^ (W - 1)) ≤ x2TgtM t2 i y2 ∧ x2TgtM t2 i y2 < 2 ^ (W - 1) :=
    fun i hi => x2TgtM_range W (by omega) t2 i y2 hi hy2
  have hpc := packCol_ent W _ (fun x2 => x2TgtM t2 x2 y2) hW1 hv
  have hb : ∀ s < x2Mult 0 t2, |x2TgtM t0 x0 y0 * x2TgtM t1 x1 y1 *
      ent W (W - 1) (packCol W (x2Mult 0 t2) (fun x2 => x2TgtM t2 x2 y2)) s| < 2 ^ (W - 1) := by
    intro s hs
    rw [hpc s hs]
    have h0 := x2TgtM_bound t0 x0 hx0 y0 hy0
    have h1 := x2TgtM_bound t1 x1 hx1 y1 hy1
    have h2 := x2TgtM_bound t2 s hs y2 hy2
    have hprod : |x2TgtM t0 x0 y0 * x2TgtM t1 x1 y1 * x2TgtM t2 s y2| ≤ 2 ^ 6 * 2 ^ 6 * 2 ^ 6 := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul h0 h1 (abs_nonneg _) (by positivity)) h2 (abs_nonneg _) (by positivity)
    have h18 : (2 : ℤ) ^ 6 * 2 ^ 6 * 2 ^ 6 < 2 ^ (W - 1) := by
      rw [← pow_add, ← pow_add]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    exact lt_of_le_of_lt hprod h18
  rw [scaleRun_ent W _ _ _ hW1 (packCol_lt W _ _ hW1 hv) hb x2 hx2, hpc x2 hx2]

theorem x2TgtCols_entry (W d : ℕ) (b : x2Key 0) (hW : 20 ≤ W) (x y : x2Amb 0 b) :
    ent W (W - 1) ((x2TgtCols W d b).getD (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) =
      x2TgtM (x2KeyTypes 0 b 0) x.1 y.1 * x2TgtM (x2KeyTypes 0 b 1) x.2.1 y.2.1 *
        x2TgtM (x2KeyTypes 0 b 2) x.2.2 y.2.2 := by
  unfold x2TgtCols
  rw [x2Flat3_val _ _ _ y, x2Cols_getD _ _ _ _ _ _ _ y.1.isLt y.2.1.isLt y.2.2.isLt, x2Flat3_val _ _ _ x]
  exact x2TgtCol_ent W d _ _ _ hW _ _ _ _ _ _ x.1.isLt x.2.1.isLt x.2.2.isLt y.1.isLt y.2.1.isLt y.2.2.isLt

/-! ### The target of a block -/

theorem x2Target_eq_of_check (D : X2Data) (b : x2Key 0) (W d : ℕ) (Jcols : List ℕ)
    (hW : 20 ≤ W) (hJc : Jcols.length = x2KeySize 0 b) (hJ : X2ImageCols D b Jcols)
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ 18) < 2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ 18) * 2 ^ 10) <
        2 ^ (W - 1)) :
    x2Target D b = Matrix.of fun (c c' : x2Col 0 b) => ((x2TgtNum W d b Jcols c c' : ℤ) : ℚ) / 8 := by
  have hJm : (D.image 0 b).map (Int.cast : ℤ → ℚ) = Matrix.of fun (x : x2Amb 0 b) (c : Fin (x2KeySize 0 b)) =>
      (ent 11 10 (Jcols.getD c 0) (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) : ℚ) := by
    ext x c
    simp only [Matrix.map_apply, Matrix.of_apply, hJ x c, x2Flat3_val, x2FlatIndex]
  have hT : (x2LocalTarget (x2KeyTypes 0 b 0) ⊗ₖ (x2LocalTarget (x2KeyTypes 0 b 1) ⊗ₖ
      x2LocalTarget (x2KeyTypes 0 b 2)) : Matrix (x2Amb 0 b) (x2Amb 0 b) ℚ) =
      Matrix.of fun (x y : x2Amb 0 b) => (ent W (W - 1) ((x2TgtCols W d b).getD
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y) 0)
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) : ℚ) / 8 := by
    ext x y
    rw [Matrix.of_apply, x2TgtCols_entry W d b hW x y]
    simp only [Matrix.kroneckerMap_apply, x2LocalTarget_apply]
    push_cast
    ring
  have hXb : ∀ i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      ∀ k < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2,
      |ent W (W - 1) ((x2TgtCols W d b).getD i 0) k| ≤ 2 ^ 18 := by
    intro i hi k hk
    obtain ⟨x, rfl⟩ : ∃ x : x2Amb 0 b,
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x : ℕ) = k :=
      ⟨(x2Flat3 _ _ _).symm ⟨k, hk⟩, by simp⟩
    obtain ⟨y, rfl⟩ : ∃ y : x2Amb 0 b,
        (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) y : ℕ) = i :=
      ⟨(x2Flat3 _ _ _).symm ⟨i, hi⟩, by simp⟩
    rw [x2TgtCols_entry W d b hW x y, abs_mul, abs_mul]
    have h0 := x2TgtM_bound _ _ x.1.isLt _ y.1.isLt
    have h1 := x2TgtM_bound _ _ x.2.1.isLt _ y.2.1.isLt
    have h2 := x2TgtM_bound _ _ x.2.2.isLt _ y.2.2.isLt
    calc |x2TgtM (x2KeyTypes 0 b 0) x.1 y.1| * |x2TgtM (x2KeyTypes 0 b 1) x.2.1 y.2.1| *
          |x2TgtM (x2KeyTypes 0 b 2) x.2.2 y.2.2| ≤ 2 ^ 6 * 2 ^ 6 * 2 ^ 6 :=
          mul_le_mul (mul_le_mul h0 h1 (abs_nonneg _) (by positivity)) h2 (abs_nonneg _) (by positivity)
      _ = 2 ^ 18 := by norm_num
  have hXlt : ∀ z ∈ x2TgtCols W d b, z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)) := by
    unfold x2TgtCols x2Cols
    exact x2o_mem_map_range _ _ (fun z => z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2)))
      (fun i _ => lt_of_lt_of_eq (colOfPieces_lt _ _ _ _ _) (by congr 1; ring))
  have hl : (x2TgtCols W d b).length = x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 := by
    unfold x2TgtCols
    exact x2Cols_length _ _ _ _
  have hJrow : ∀ (x : x2Amb 0 b) (c : ℕ), c < x2KeySize 0 b →
      ent W (W - 1) ((jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols
        (fun i => i)).getD (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) 0) c =
        ent 11 10 (Jcols.getD c 0) (x2Flat3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2) x) := by
    intro x c hc
    rw [jRows_ent W _ _ Jcols _ _ c (by omega) (Fin.isLt _) hc]
  unfold x2Target
  simp only []
  rw [hJm, hT]
  ext c c'
  rw [x2PartProj W _ _ (x2Flat3 _ _ _) (x2Flat3 _ _ _) Jcols (x2TgtCols W d b)
      (jRows W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) Jcols (fun i => i))
      8 (2 ^ 18) (by omega) hJc hl (jRows_length _ _ _ _ _) hXlt (jRows_lt _ _ _ _ _ (by omega)) hXb (by positivity)
      hJrow (jRows_bound _ _ _ _ _ (by omega)) hb1 hb2 c c']
  simp only [Matrix.of_apply]
  rfl

/-- With a kernel check of the numerators: `x2Target D b = T8 / 8`. -/
theorem x2Target_eq_lit (D : X2Data) (b : x2Key 0) (W d : ℕ) (Jcols : List ℕ) (T8 : ℕ → ℕ → ℤ)
    (h : x2Target D b = Matrix.of fun (c c' : x2Col 0 b) => ((x2TgtNum W d b Jcols c c' : ℤ) : ℚ) / 8)
    (hchk : ∀ c < x2KeySize 0 b, ∀ c' < x2KeySize 0 b, x2TgtNum W d b Jcols c c' = T8 c c') :
    x2Target D b = Matrix.of fun (c c' : x2Col 0 b) => ((T8 c c' : ℤ) : ℚ) / 8 := by
  rw [h]
  ext c c'
  simp only [Matrix.of_apply]
  rw [hchk c c.isLt c' c'.isLt]

end X2
end ThreeCopyQutritWerner
