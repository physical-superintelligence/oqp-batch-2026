module

public import ThreeCopyQutritWerner.CertificateX2OutFast
public import ThreeCopyQutritWerner.CertificateX2OutputTarget

@[expose] public section


/-!
# Output stage: chunked targets `x2Target D b`

`8 x2Target D b = Jᵀ (M₀ ⊗ M₁ ⊗ M₂) J` (`M_t = 2 G_t - D_t`, `x2TgtM`). As for the outputs (CertificateX2OutFast), the rows
are taken in chunks `x₂ = a` (slot `x₁ m₀ + x₀`); a chunk column is a list of `m₁` scaled copies of the packed column
`M₀[·, y₀]` (`scaleRun`, scalar `M₁[x₁, y₁] M₂[a, y₂]`), and `x2ChunkO` projects the chunk. `x2FTOK` checks a chunk against
a literal computed at build time; `x2Target_of_chunks` assembles `x2Target D b = O / 8`.
-/

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner
namespace X2

/-- `M₀ ⊗ M₁ ⊗ M₂` on coordinates. -/
def x2XT (b : x2Key 0) (x0 x1 x2 y0 y1 y2 : ℕ) : ℤ :=
  x2TgtM (x2KeyTypes 0 b 0) x0 y0 * x2TgtM (x2KeyTypes 0 b 1) x1 y1 * x2TgtM (x2KeyTypes 0 b 2) x2 y2

/-- Packed column `y₀` of `M_{t₀}`. -/
def x2FTP0 (W : ℕ) (b : x2Key 0) (y0 : ℕ) : ℕ :=
  packCol W (x2KeyMult 0 b 0) (fun x0 => x2TgtM (x2KeyTypes 0 b 0) x0 y0)

/-- Pieces of the target column `(y₀, y₁, y₂)` in the chunk `x₂ = a`, one per `x₁`. -/
def x2FTG (W : ℕ) (b : x2Key 0) (a y0 y1 y2 : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 1)).map fun x1 =>
    scaleRun W (x2KeyMult 0 b 0) (x2TgtM (x2KeyTypes 0 b 1) x1 y1 * x2TgtM (x2KeyTypes 0 b 2) a y2) (x2FTP0 W b y0)

def x2FTCol (W : ℕ) (b : x2Key 0) (a y0 y1 y2 : ℕ) : ℕ :=
  concatFibers W (x2KeyMult 0 b 0) ((x2FTG W b a y0 y1 y2).map (runOf W (x2KeyMult 0 b 0) 0))

def x2FTXC (W : ℕ) (b : x2Key 0) (a : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).flatMap fun y0 => (List.range (x2KeyMult 0 b 1)).flatMap fun y1 =>
    (List.range (x2KeyMult 0 b 2)).map fun y2 => x2FTCol W b a y0 y1 y2

noncomputable def x2FTOK (W : ℕ) (b : x2Key 0) (Jd : List (List ℕ)) (Jcols : List ℕ) (a : ℕ) (lit : List ℕ) : Bool :=
  decide (x2ChunkO W (x2KeySize 0 b) (x2KeyMult 0 b 1 * x2KeyMult 0 b 0) Jd (x2FTXC W b a) (x2F0JR W b Jcols a) = lit)

def x2FTOC (W : ℕ) (b : x2Key 0) (Jd : List (List ℕ)) (Jcols : List ℕ) (a : ℕ) : List ℕ :=
  x2ChunkOC W (x2KeySize 0 b) (x2KeyMult 0 b 1 * x2KeyMult 0 b 0) Jd (x2FTXC W b a) (x2F0JR W b Jcols a)

theorem x2XT_bound (b : x2Key 0) (x0 x1 x2 y0 y1 y2 : ℕ) (hx0 : x0 < x2KeyMult 0 b 0) (hx1 : x1 < x2KeyMult 0 b 1)
    (hx2 : x2 < x2KeyMult 0 b 2) (hy0 : y0 < x2KeyMult 0 b 0) (hy1 : y1 < x2KeyMult 0 b 1)
    (hy2 : y2 < x2KeyMult 0 b 2) : |x2XT b x0 x1 x2 y0 y1 y2| ≤ 2 ^ 18 := by
  unfold x2XT
  rw [abs_mul, abs_mul]
  have h0 := x2TgtM_bound _ x0 hx0 y0 hy0
  have h1 := x2TgtM_bound _ x1 hx1 y1 hy1
  have h2 := x2TgtM_bound _ x2 hx2 y2 hy2
  calc |x2TgtM (x2KeyTypes 0 b 0) x0 y0| * |x2TgtM (x2KeyTypes 0 b 1) x1 y1| * |x2TgtM (x2KeyTypes 0 b 2) x2 y2|
      ≤ 2 ^ 6 * 2 ^ 6 * 2 ^ 6 :=
        mul_le_mul (mul_le_mul h0 h1 (abs_nonneg _) (by positivity)) h2 (abs_nonneg _) (by positivity)
    _ = 2 ^ 18 := by norm_num

theorem x2FTXC_ent (W : ℕ) (b : x2Key 0) (a : ℕ) (hW : 20 ≤ W) (ha : a < x2KeyMult 0 b 2)
    (y0 y1 y2 x0 x1 : ℕ) (hy0 : y0 < x2KeyMult 0 b 0) (hy1 : y1 < x2KeyMult 0 b 1) (hy2 : y2 < x2KeyMult 0 b 2)
    (hx0 : x0 < x2KeyMult 0 b 0) (hx1 : x1 < x2KeyMult 0 b 1) :
    ent W (W - 1) ((x2FTXC W b a).getD (x2Fl b y0 y1 y2) 0) (x1 * x2KeyMult 0 b 0 + x0) =
      x2XT b x0 x1 a y0 y1 y2 := by
  have hW1 : 1 ≤ W := by omega
  have hq : x1 < (x2FTG W b a y0 y1 y2).length := by simp [x2FTG]; exact hx1
  unfold x2FTXC x2Fl
  rw [xf_nested_getD _ _ _ (fun y0 y1 y2 => x2FTCol W b a y0 y1 y2) y0 y1 y2 hy0 hy1 hy2]
  unfold x2FTCol
  rw [xf_col_ent W (x2KeyMult 0 b 0) (x2FTG W b a y0 y1 y2) 0 x1 x0 hq hx0, zero_add]
  unfold x2FTG
  rw [x2o_getD_map_range _ x1 _ hx1]
  have hv : ∀ i < x2KeyMult 0 b 0, -(2 ^ (W - 1)) ≤ x2TgtM (x2KeyTypes 0 b 0) i y0 ∧
      x2TgtM (x2KeyTypes 0 b 0) i y0 < 2 ^ (W - 1) :=
    fun i hi => x2TgtM_range W (by omega) _ i y0 hi hy0
  have hpc := packCol_ent W _ (fun x0 => x2TgtM (x2KeyTypes 0 b 0) x0 y0) hW1 hv
  have hb : ∀ s < x2KeyMult 0 b 0, |x2TgtM (x2KeyTypes 0 b 1) x1 y1 * x2TgtM (x2KeyTypes 0 b 2) a y2 *
      ent W (W - 1) (x2FTP0 W b y0) s| < 2 ^ (W - 1) := by
    intro s hs
    unfold x2FTP0
    rw [hpc s hs]
    have hx := x2XT_bound b s x1 a y0 y1 y2 hs hx1 ha hy0 hy1 hy2
    unfold x2XT at hx
    have h18 : (2 : ℤ) ^ 18 < 2 ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    calc |x2TgtM (x2KeyTypes 0 b 1) x1 y1 * x2TgtM (x2KeyTypes 0 b 2) a y2 * x2TgtM (x2KeyTypes 0 b 0) s y0|
        = |x2TgtM (x2KeyTypes 0 b 0) s y0 * x2TgtM (x2KeyTypes 0 b 1) x1 y1 * x2TgtM (x2KeyTypes 0 b 2) a y2| := by
          congr 1; ring
      _ ≤ 2 ^ 18 := hx
      _ < 2 ^ (W - 1) := h18
  rw [scaleRun_ent W _ _ (x2FTP0 W b y0) hW1 (packCol_lt W _ _ hW1 hv) hb x0 hx0]
  unfold x2FTP0
  rw [hpc x0 hx0]
  unfold x2XT
  ring

theorem x2FTOK_sound (W : ℕ) (b : x2Key 0) (Jd : List (List ℕ)) (Jcols : List ℕ) (a : ℕ) (lit : List ℕ)
    (hW : 20 ≤ W) (ha : a < x2KeyMult 0 b 2) (hJc : Jcols.length = x2KeySize 0 b)
    (hJd : ∀ c < x2KeySize 0 b,
      Jd.getD c [] = digs 11 (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (Jcols.getD c 0))
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ 18) < 2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 1 * x2KeyMult 0 b 0 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ 18) * 2 ^ 10) < 2 ^ (W - 1))
    (hok : x2FTOK W b Jd Jcols a lit = true) (c c' : ℕ) (hc : c < x2KeySize 0 b) (hc' : c' < x2KeySize 0 b) :
    ent W (W - 1) (lit.getD c' 0) c =
      ∑ x1 ∈ Finset.range (x2KeyMult 0 b 1), ∑ x0 ∈ Finset.range (x2KeyMult 0 b 0),
        ent 11 10 (Jcols.getD c 0) (x2Fl b x0 x1 a) *
          ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
            x2XT b x0 x1 a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i := by
  have hW12 : 12 ≤ W := by omega
  unfold x2FTOK at hok
  simp only [decide_eq_true_eq] at hok
  rw [← hok]
  have hent : ∀ i, i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 → ∀ s,
      s < x2KeyMult 0 b 1 * x2KeyMult 0 b 0 →
      ent W (W - 1) ((x2FTXC W b a).getD i 0) s =
          x2XT b (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) ∧
        |x2XT b (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i)| ≤ 2 ^ 18 := by
    intro i hi s hs
    obtain ⟨hd0, hd1, hd2, hfl⟩ := x2Dec_lt b i hi
    obtain ⟨hq, hr, hqr⟩ := xf_mod_div s (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) hs
    have h := x2FTXC_ent W b a hW ha (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) (s % x2KeyMult 0 b 0)
      (s / x2KeyMult 0 b 0) hd0 hd1 hd2 hr hq
    rw [hfl, hqr] at h
    exact ⟨h, x2XT_bound b _ _ _ _ _ _ hr hq ha hd0 hd1 hd2⟩
  rw [x2ChunkProj W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b)
      (x2KeyMult 0 b 1 * x2KeyMult 0 b 0) Jcols Jd (x2FTXC W b a) (x2F0JR W b Jcols a)
      (fun s i => x2XT b (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i))
      (fun s c => ent 11 10 (Jcols.getD c 0) (x2Fl b (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a))
      (2 ^ 18) hW12 (by positivity) hJd
      (by unfold x2FTXC; exact xf_nested_length _ _ _ _)
      (by
        unfold x2FTXC
        exact xf_nested_mem _ _ _ (fun y0 y1 y2 => x2FTCol W b a y0 y1 y2)
          (fun z => z < 2 ^ (W * (x2KeyMult 0 b 1 * x2KeyMult 0 b 0)))
          (fun y0 y1 y2 => xf_col_lt W (x2KeyMult 0 b 0) (x2FTG W b a y0 y1 y2) 0 (x2KeyMult 0 b 1) (by simp [x2FTG])))
      (fun i hi s hs => (hent i hi s hs).1) (fun i hi s hs => (hent i hi s hs).2)
      (by unfold x2F0JR; exact xf_rows_length _ _ _)
      (by
        unfold x2F0JR
        exact xf_rows_mem _ _ (fun x1 x0 => jRowF W Jcols (x2Fl b x0 x1 a)) (fun z => z < 2 ^ (W * x2KeySize 0 b))
          (fun u v => by (try beta_reduce); rw [← hJc]; exact jRowF_lt W Jcols _ hW12))
      (by
        intro s hs c hc
        unfold x2F0JR
        rw [xf_rows_getD _ _ (fun x1 x0 => jRowF W Jcols (x2Fl b x0 x1 a)) s hs]
        exact jRowF_ent W Jcols _ c hW12 (by rw [hJc]; exact hc))
      (fun s _ c _ => ent11_abs_le _ _) hb1 hb2 c c' hc hc']
  rw [xf_sum_range_mul _ (x2KeyMult 0 b 0) (x2KeyMult 0 b 1)]
  apply Finset.sum_congr rfl
  intro x1 _
  apply Finset.sum_congr rfl
  intro x0 hx0
  rw [Finset.mem_range] at hx0
  obtain ⟨hdv, hmd⟩ := x2o_divmod x1 x0 (x2KeyMult 0 b 0) hx0
  simp only [hdv, hmd]

/-- `Σ_x Σ_y J[x, c] X[x, y] J[y, c']` over the ambient equals `x2PartT` (sums over naturals). -/
theorem xf_double_partT (b : x2Key 0) (Jcols : List ℕ) (X : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (c c' : ℕ) :
    ∑ x : x2Amb 0 b, ∑ y : x2Amb 0 b, ent 11 10 (Jcols.getD c 0) (x2Fl b x.1 x.2.1 x.2.2) *
      (X x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 * ent 11 10 (Jcols.getD c' 0) (x2Fl b y.1 y.2.1 y.2.2)) =
      x2PartT b Jcols X c c' := by
  have hy : ∀ x : x2Amb 0 b, ∑ y : x2Amb 0 b, ent 11 10 (Jcols.getD c 0) (x2Fl b x.1 x.2.1 x.2.2) *
      (X x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 * ent 11 10 (Jcols.getD c' 0) (x2Fl b y.1 y.2.1 y.2.2)) =
      ent 11 10 (Jcols.getD c 0) (x2Fl b x.1 x.2.1 x.2.2) *
        ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
          X x.1 x.2.1 x.2.2 (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i := by
    intro x
    rw [← Finset.mul_sum]
    congr 1
    refine (xf_sum_amb_flat (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)
      (fun y0 y1 y2 => X x.1 x.2.1 x.2.2 y0 y1 y2 * ent 11 10 (Jcols.getD c' 0) (x2Fl b y0 y1 y2))).trans ?_
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hfl := (x2Dec_lt b i hi).2.2.2
    try beta_reduce
    unfold x2Dec0 x2Dec1 x2Dec2 at hfl ⊢
    rw [hfl]
  rw [Finset.sum_congr rfl (fun x _ => hy x)]
  rw [xf_sum_amb3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)
    (fun x0 x1 x2 => ent 11 10 (Jcols.getD c 0) (x2Fl b x0 x1 x2) *
      ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
        X x0 x1 x2 (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i)]
  rfl

theorem x2Target_eq_partT (D : X2Data) (b : x2Key 0) (Jcols : List ℕ) (hJ : X2ImageCols D b Jcols)
    (c c' : x2Col 0 b) : x2Target D b c c' = ((x2PartT b Jcols (x2XT b) c c' : ℤ) : ℚ) / 8 := by
  have hJx : ∀ (x : x2Amb 0 b) (k : x2Col 0 b), ((D.image 0 b).map (Int.cast : ℤ → ℚ)) x k =
      ((ent 11 10 (Jcols.getD k 0) (x2Fl b x.1 x.2.1 x.2.2) : ℤ) : ℚ) := by
    intro x k
    rw [Matrix.map_apply, hJ x k]
    rfl
  have hT : ∀ x y : x2Amb 0 b, (x2LocalTarget (x2KeyTypes 0 b 0) ⊗ₖ (x2LocalTarget (x2KeyTypes 0 b 1) ⊗ₖ
      x2LocalTarget (x2KeyTypes 0 b 2)) : Matrix (x2Amb 0 b) (x2Amb 0 b) ℚ) x y =
      ((x2XT b x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 : ℤ) : ℚ) / 8 := by
    intro x y
    simp only [Matrix.kroneckerMap_apply, x2LocalTarget_apply]
    unfold x2XT
    push_cast
    ring
  have key : x2Target D b c c' = ((∑ x : x2Amb 0 b, ∑ y : x2Amb 0 b,
      ent 11 10 (Jcols.getD c 0) (x2Fl b x.1 x.2.1 x.2.2) *
        (x2XT b x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 * ent 11 10 (Jcols.getD c' 0) (x2Fl b y.1 y.2.1 y.2.2)) : ℤ) : ℚ) /
        8 := by
    unfold x2Target
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hJx, hT, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    push_cast
    ring
  rw [key, xf_double_partT]

/-- `x2Target` of block `b` from chunk literals. -/
theorem x2Target_of_chunks (D : X2Data) (b : x2Key 0) (W : ℕ) (Jd : List (List ℕ)) (Jcols : List ℕ)
    (LT : List (List ℕ)) (O : Matrix (x2Col 0 b) (x2Col 0 b) ℤ) (hJ : X2ImageCols D b Jcols) (hW : 20 ≤ W)
    (hJc : Jcols.length = x2KeySize 0 b)
    (hJd : ∀ c < x2KeySize 0 b,
      Jd.getD c [] = digs 11 (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (Jcols.getD c 0))
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ 18) < 2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 1 * x2KeyMult 0 b 0 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ 18) * 2 ^ 10) < 2 ^ (W - 1))
    (hok : ∀ a < x2KeyMult 0 b 2, x2FTOK W b Jd Jcols a (LT.getD a []) = true)
    (hsum : (Matrix.of fun (c c' : x2Col 0 b) =>
      rsum (fun a => ent W (W - 1) ((LT.getD a []).getD c' 0) c) (x2KeyMult 0 b 2)) = O) :
    x2Target D b = Matrix.of fun (c c' : x2Col 0 b) => ((O c c' : ℤ) : ℚ) / 8 := by
  ext c c'
  rw [x2Target_eq_partT D b Jcols hJ c c', Matrix.of_apply, ← hsum, Matrix.of_apply]
  congr 2
  rw [rsum_eq]
  unfold x2PartT
  rw [xf_reorder0]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_range] at ha
  rw [x2FTOK_sound W b Jd Jcols a _ hW ha hJc hJd hb1 hb2 (hok a ha) c c' c.isLt c'.isLt]

end X2
end ThreeCopyQutritWerner
