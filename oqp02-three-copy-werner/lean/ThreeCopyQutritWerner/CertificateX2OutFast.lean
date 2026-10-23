module

public import ThreeCopyQutritWerner.CertificateX2OutputIface

@[expose] public section


/-!
# Output stage: chunked reading of `x2Out` from row tables

The expanded axis-0 tables are row tables `T : List (List ℕ)` (`xfTab T k j = (T.getD k []).getD j 0`,
row `k` = axis-2 label, entry `j` = axis-1 label, `513` slots of width `W`, offset `2^(W-1)`).

On an h block `b` (types `t₀ ≤ t₁ ≤ t₂`, multiplicities `m₀, m₁, m₂`, `N = m₀ m₁ m₂`, `r` image columns) the reading
`x2RawH` is the sum of three integer parts `X₀`, `X₁`, `X₂` (`x2X0`, `x2X1`, `x2X2`), and
`Jᵀ X_P J` is computed by chunks of rows: a chunk fixes the value `a` of the site whose label indexes the table row
(`x₂` for parts 0 and 1, `x₁` for part 2). A chunk needs only the table rows of that site value; they are cut once into
triangles of sub-fibers (`triRows`, `rowSub`), so the kernel never searches a long list per entry; the chunk columns
(`x2F0XC`, ...) are built by nested maps whose shared subterms the kernel evaluates once. `x2ChunkO` projects a chunk
(`Y = X J` on the chunk rows, then `J_chunkᵀ Y`), and `x2ChunkProj` states its value. A chunk is checked against a
literal (`x2F0OK`, ...) whose value is computed at build time (`CertificateX2OutFastMeta`); `x2Out_of_chunks` assembles
`x2Out` from the chunk literals and a final integer check.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### List and sum helpers -/

/-- Entry `(k, j)` of a row table (the `xfTab`, under this file's own name). -/
def xfTab (T : List (List ℕ)) (k j : ℕ) : ℕ := (T.getD k []).getD j 0

theorem xf_getD_take (l : List ℕ) (n i : ℕ) (hi : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  congr 1
  first
  | exact List.getElem?_take_of_lt hi
  | simp [List.getElem?_take, hi]

theorem xf_getD_drop (l : List ℕ) (n i : ℕ) : (l.drop n).getD i 0 = l.getD (n + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  congr 1
  first
  | exact List.getElem?_drop l n i
  | simp [List.getElem?_drop]
  | simp

theorem xf_getD_map_zero (f : ℕ → ℕ) (hf : f 0 = 0) (l : List ℕ) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hf]

theorem runOf_zero (W L u : ℕ) : runOf W L u 0 = 0 := by
  simp [runOf]

/-- `cumT m i = ∑_{j < i} (m - j)`: start of row `i` of a triangle with rows of lengths `m, m-1, ...`. -/
def cumT (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => cumT m i + (m - i)

theorem cumT_succ' (m : ℕ) : ∀ i, cumT m (i + 1) = m + cumT (m - 1) i
  | 0 => by simp [cumT]
  | i + 1 => by
    have h1 : cumT m (i + 1 + 1) = cumT m (i + 1) + (m - (i + 1)) := rfl
    have h2 : cumT (m - 1) (i + 1) = cumT (m - 1) i + (m - 1 - i) := rfl
    rw [h1, h2, cumT_succ' m i]
    omega

theorem cumT_mono (m : ℕ) : ∀ {i j : ℕ}, i ≤ j → cumT m i ≤ cumT m j := by
  intro i j hij
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have := ih (by omega)
      show cumT m i ≤ cumT m j + (m - j)
      omega
    · have : i = j + 1 := by omega
      subst this
      exact le_refl _

theorem cumT_lt (m i d : ℕ) (hi : i < m) (hd : d < m - i) : cumT m i + d < cumT m m := by
  have h1 : cumT m (i + 1) = cumT m i + (m - i) := rfl
  have h2 := cumT_mono m (show i + 1 ≤ m by omega)
  omega

/-- Rows of a triangle: `L` rows, of lengths `m, m - 1, ...`. -/
def triRows : ℕ → ℕ → List ℕ → List (List ℕ)
  | 0, _, _ => []
  | L + 1, m, l => l.take m :: triRows L (m - 1) (l.drop m)

theorem triRows_getD : ∀ (L m : ℕ) (l : List ℕ) (i d : ℕ), i < L → d < m - i →
    ((triRows L m l).getD i []).getD d 0 = l.getD (cumT m i + d) 0
  | 0, _, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | L + 1, m, l, 0, d, _, hd => by
    have e : (triRows (L + 1) m l).getD 0 [] = l.take m := rfl
    rw [e, xf_getD_take l m d (by omega)]
    simp [cumT]
  | L + 1, m, l, i + 1, d, hi, hd => by
    have e : (triRows (L + 1) m l).getD (i + 1) [] = (triRows L (m - 1) (l.drop m)).getD i [] := rfl
    rw [e, triRows_getD L (m - 1) (l.drop m) i d (by omega) (by omega), xf_getD_drop, cumT_succ']
    congr 1
    omega

/-- Entries `[j₀, j₀ + n)` of a table row, each cut to the slots `[u, u + L)`. -/
def rowSub (W L u j0 n : ℕ) (row : List ℕ) : List ℕ := ((row.drop j0).take n).map (runOf W L u)

theorem rowSub_getD (W L u j0 n : ℕ) (row : List ℕ) (i : ℕ) (hi : i < n) :
    (rowSub W L u j0 n row).getD i 0 = runOf W L u (row.getD (j0 + i) 0) := by
  unfold rowSub
  rw [xf_getD_map_zero _ (runOf_zero W L u), xf_getD_take _ _ _ hi, xf_getD_drop]

theorem xf_getD_flatMap_range' (k : ℕ) (f : ℕ → List ℕ) (hf : ∀ i, (f i).length = k) :
    ∀ (n s i j : ℕ), i < n → j < k → ((List.range' s n).flatMap f).getD (i * k + j) 0 = (f (s + i)).getD j 0
  | 0, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, s, 0, j, _, hj => by
    rw [List.range'_succ, List.flatMap_cons, zero_mul, zero_add, add_zero]
    rw [List.getD_append _ _ _ _ (by rw [hf s]; exact hj)]
  | n + 1, s, i + 1, j, hi, hj => by
    rw [List.range'_succ, List.flatMap_cons]
    rw [List.getD_append_right _ _ _ _ (by rw [hf s]; nlinarith)]
    rw [hf s, show (i + 1) * k + j - k = i * k + j by rw [add_mul, one_mul]; omega]
    rw [xf_getD_flatMap_range' k f hf n (s + 1) i j (by omega) hj]
    congr 2
    omega

theorem xf_getD_flatMap_range (k : ℕ) (f : ℕ → List ℕ) (hf : ∀ i, (f i).length = k) (n i j : ℕ) (hi : i < n)
    (hj : j < k) : ((List.range n).flatMap f).getD (i * k + j) 0 = (f i).getD j 0 := by
  rw [List.range_eq_range', xf_getD_flatMap_range' k f hf n 0 i j hi hj, zero_add]

theorem xf_length_flatMap_range' (k : ℕ) (f : ℕ → List ℕ) (hf : ∀ i, (f i).length = k) :
    ∀ (n s : ℕ), ((List.range' s n).flatMap f).length = n * k
  | 0, _ => by simp
  | n + 1, s => by
    rw [List.range'_succ, List.flatMap_cons, List.length_append, hf s,
      xf_length_flatMap_range' k f hf n (s + 1)]
    ring

theorem xf_length_flatMap_range (k : ℕ) (f : ℕ → List ℕ) (hf : ∀ i, (f i).length = k) (n : ℕ) :
    ((List.range n).flatMap f).length = n * k := by
  rw [List.range_eq_range', xf_length_flatMap_range' k f hf n 0]

theorem xf_mem_flatMap_range (f : ℕ → List ℕ) (P : ℕ → Prop) (h : ∀ i x, x ∈ f i → P x) (n : ℕ) :
    ∀ x ∈ (List.range n).flatMap f, P x := by
  intro x hx
  rw [List.mem_flatMap] at hx
  obtain ⟨i, _, hi⟩ := hx
  exact h i x hi

/-- `∑_{s < n m} f s = ∑_{i < n} ∑_{j < m} f (i m + j)`. -/
theorem xf_sum_range_mul (f : ℕ → ℤ) (m : ℕ) : ∀ n : ℕ,
    ∑ s ∈ Finset.range (n * m), f s = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, f (i * m + j)
  | 0 => by simp
  | n + 1 => by
    rw [add_mul, one_mul, Finset.sum_range_add, xf_sum_range_mul f m n, Finset.sum_range_succ]

/-- A recursive sum (kernel friendly). -/
def rsum (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => rsum f n + f n

theorem rsum_eq (f : ℕ → ℤ) : ∀ n, rsum f n = ∑ a ∈ Finset.range n, f a
  | 0 => by simp [rsum]
  | n + 1 => by rw [rsum, rsum_eq f n, Finset.sum_range_succ]

/-! ### Labels as triangle positions (kernel checks over all types) -/

theorem x2SIdx_formula_bool : ∀ t : Fin 8, ∀ a < x2Mult 0 t, ∀ b < x2Mult 0 t,
    Nat.beq (x2SIdx 0 t a b : ℕ) (x2SOff 0 t + cumT (x2Mult 0 t) (min a b) + (max a b - min a b)) = true := by
  decide +kernel

theorem x2AIdx_formula_bool : ∀ t : Fin 8, ∀ a < x2Mult 0 t, ∀ b < x2Mult 0 t,
    (Nat.beq a b || Nat.beq (x2AIdx 0 t a b : ℕ)
      (x2AOff 0 t + cumT (x2Mult 0 t - 1) (min a b) + (max a b - min a b - 1))) = true := by
  decide +kernel

theorem x2SIdx_formula (t : Fin 8) (a b : ℕ) (ha : a < x2Mult 0 t) (hb : b < x2Mult 0 t) :
    (x2SIdx 0 t a b : ℕ) = x2SOff 0 t + cumT (x2Mult 0 t) (min a b) + (max a b - min a b) := by
  have h := x2SIdx_formula_bool t a ha b hb
  simpa only [Nat.beq_eq] using h

theorem x2AIdx_formula (t : Fin 8) (a b : ℕ) (ha : a < x2Mult 0 t) (hb : b < x2Mult 0 t) (hab : a ≠ b) :
    (x2AIdx 0 t a b : ℕ) = x2AOff 0 t + cumT (x2Mult 0 t - 1) (min a b) + (max a b - min a b - 1) := by
  have h := x2AIdx_formula_bool t a ha b hb
  simp only [Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h
  · exact absurd h hab
  · exact h

/-! ### Triangles of sub-fibers -/

/-- Entry `(x, y)` of a symmetric triangle (S labels). -/
def triS (R : List (List ℕ)) (x y : ℕ) : ℕ := (R.getD (min x y) []).getD (max x y - min x y) 0

/-- Entry `(x, y)`, `x ≠ y`, of an antisymmetric triangle (A labels). -/
def triA (R : List (List ℕ)) (x y : ℕ) : ℕ := (R.getD (min x y) []).getD (max x y - min x y - 1) 0

/-- S triangle of table row `k`: the type-`tc` labels, cut to `L` slots from `u`. -/
def triSOf (W L u : ℕ) (tc : Fin 8) (T : List (List ℕ)) (k : ℕ) : List (List ℕ) :=
  triRows (x2Mult 0 tc) (x2Mult 0 tc)
    (rowSub W L u (x2SOff 0 tc) (cumT (x2Mult 0 tc) (x2Mult 0 tc)) (T.getD k []))

/-- A triangle of table row `k`: the type-`tc` labels, cut to `L` slots from `u`. -/
def triAOf (W L u : ℕ) (tc : Fin 8) (T : List (List ℕ)) (k : ℕ) : List (List ℕ) :=
  triRows (x2Mult 0 tc) (x2Mult 0 tc - 1)
    (rowSub W L u (x2AOff 0 tc) (cumT (x2Mult 0 tc - 1) (x2Mult 0 tc)) (T.getD k []))

theorem triS_eq (W L u : ℕ) (tc : Fin 8) (T : List (List ℕ)) (k x y : ℕ) (hx : x < x2Mult 0 tc)
    (hy : y < x2Mult 0 tc) : triS (triSOf W L u tc T k) x y = runOf W L u (xfTab T k (x2SIdx 0 tc x y)) := by
  have hmn : min x y < x2Mult 0 tc := lt_of_le_of_lt (min_le_left x y) hx
  have hmx : max x y < x2Mult 0 tc := max_lt hx hy
  have hle : min x y ≤ max x y := min_le_max
  have hd : max x y - min x y < x2Mult 0 tc - min x y := by omega
  unfold triS triSOf xfTab
  rw [triRows_getD _ _ _ _ _ hmn hd,
    rowSub_getD _ _ _ _ _ _ _ (cumT_lt _ _ _ hmn hd), x2SIdx_formula tc x y hx hy]
  congr 2
  omega

theorem triA_eq (W L u : ℕ) (tc : Fin 8) (T : List (List ℕ)) (k x y : ℕ) (hx : x < x2Mult 0 tc)
    (hy : y < x2Mult 0 tc) (hxy : x ≠ y) :
    triA (triAOf W L u tc T k) x y = runOf W L u (xfTab T k (x2AIdx 0 tc x y)) := by
  have hmn : min x y < x2Mult 0 tc - 1 := by
    rcases le_total x y with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  have hmx : max x y < x2Mult 0 tc := max_lt hx hy
  have hlt : min x y < max x y := by
    rcases lt_or_gt_of_ne hxy with h | h
    · rw [min_eq_left h.le, max_eq_right h.le]; exact h
    · rw [min_eq_right h.le, max_eq_left h.le]; exact h
  have hd : max x y - min x y - 1 < x2Mult 0 tc - 1 - min x y := by omega
  have hn : cumT (x2Mult 0 tc - 1) (min x y) + (max x y - min x y - 1) < cumT (x2Mult 0 tc - 1) (x2Mult 0 tc) :=
    lt_of_lt_of_le (cumT_lt _ _ _ hmn hd) (cumT_mono _ (by omega))
  unfold triA triAOf xfTab
  rw [triRows_getD _ _ _ _ _ (by omega) hd, rowSub_getD _ _ _ _ _ _ _ hn, x2AIdx_formula tc x y hx hy hxy]
  congr 2
  omega

/-! ### Image rows (one pass over the packed columns) -/

/-- Row of the image at flat position `p`, `W`-bit slots, offset `2^(W-1)`. -/
def jRowF (W : ℕ) (Jcols : List ℕ) (p : ℕ) : ℕ :=
  concatFibers W 1 (Jcols.map fun col => dig 11 col p + 2 ^ (W - 1) - 2 ^ 10)

theorem jRowF_eq (W : ℕ) (Jcols : List ℕ) (p : ℕ) : jRowF W Jcols p = jRowOf W Jcols.length Jcols p := by
  have h : (Jcols.map fun col => dig 11 col p + 2 ^ (W - 1) - 2 ^ 10) =
      (List.range Jcols.length).map (fun c => dig 11 (Jcols.getD c 0) p + 2 ^ (W - 1) - 2 ^ 10) := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ (by simpa using h2)]
  unfold jRowF jRowOf
  rw [h]

/-! ### Chunk projection -/

/-- Computable output of a natural linear-combination check (equal to `natAxpyRes`). -/
def natAxpyResC (W L oA : ℕ) (as' Es : List ℕ) : ℕ :=
  Nat.land (natDot as' (natFibers W L Es) + natAxpyCorr W L oA Es) (2 ^ (W * L) - 1)

/-- Column `c'` of `Y = X J` on the chunk rows (scalars: the digits of image column `c'`). -/
noncomputable def x2ChunkY (W L : ℕ) (Jd : List (List ℕ)) (XC : List ℕ) (c' : ℕ) : ℕ :=
  natAxpyRes W L 10 (Jd.getD c' []) XC

/-- Columns `c' < r` of `J_chunkᵀ Y` (scalars: the slots of `Y`, fibers: the image rows of the chunk). -/
noncomputable def x2ChunkO (W r L : ℕ) (Jd : List (List ℕ)) (XC JR : List ℕ) : List ℕ :=
  (List.range r).map fun c' => natAxpyRes W r (W - 1) (digs W L (x2ChunkY W L Jd XC c')) JR

/-- Computable twin of `x2ChunkO` (build-time candidates). -/
def x2ChunkOC (W r L : ℕ) (Jd : List (List ℕ)) (XC JR : List ℕ) : List ℕ :=
  (List.range r).map fun c' => natAxpyResC W r (W - 1) (digs W L (natAxpyResC W L 10 (Jd.getD c' []) XC)) JR

theorem x2ChunkProj (W N r L : ℕ) (Jcols : List ℕ) (Jd : List (List ℕ)) (XC JR : List ℕ)
    (X : ℕ → ℕ → ℤ) (Jrow : ℕ → ℕ → ℤ) (Xb : ℤ) (hW : 12 ≤ W) (hXb0 : 0 ≤ Xb)
    (hJd : ∀ c < r, Jd.getD c [] = digs 11 N (Jcols.getD c 0))
    (hXlen : XC.length = N) (hXlt : ∀ z ∈ XC, z < 2 ^ (W * L))
    (hXent : ∀ i < N, ∀ s < L, ent W (W - 1) (XC.getD i 0) s = X s i)
    (hXb : ∀ i < N, ∀ s < L, |X s i| ≤ Xb)
    (hJRlen : JR.length = L) (hJRlt : ∀ z ∈ JR, z < 2 ^ (W * r))
    (hJR : ∀ s < L, ∀ c < r, ent W (W - 1) (JR.getD s 0) c = Jrow s c)
    (hJRb : ∀ s < L, ∀ c < r, |Jrow s c| ≤ 2 ^ 10)
    (hb1 : (N : ℤ) * (2 ^ 10 * Xb) < 2 ^ (W - 1))
    (hb2 : (L : ℤ) * ((N : ℤ) * (2 ^ 10 * Xb) * 2 ^ 10) < 2 ^ (W - 1))
    (c c' : ℕ) (hc : c < r) (hc' : c' < r) :
    ent W (W - 1) ((x2ChunkO W r L Jd XC JR).getD c' 0) c =
      ∑ s ∈ Finset.range L, Jrow s c * ∑ i ∈ Finset.range N, X s i * ent 11 10 (Jcols.getD c' 0) i := by
  have hW2 : 2 ≤ W := by omega
  have hJdl : (Jd.getD c' []).length = N := by rw [hJd c' hc', digs_length]
  -- the scalars of the `Y` stage are the image digits
  have hJdig : ∀ i < N, (((Jd.getD c' []).getD i 0 : ℕ) : ℤ) - 2 ^ 10 = ent 11 10 (Jcols.getD c' 0) i := by
    intro i hi
    rw [hJd c' hc', digs_getD 11 N _ i hi]
    rfl
  have hJabs : ∀ i < N, |ent 11 10 (Jcols.getD c' 0) i| ≤ 2 ^ 10 := fun i _ => ent11_abs_le _ _
  -- the linear combination of the `Y` stage, slot by slot
  have hlin : ∀ s, s < L → lincomb W (sScalars 10 (Jd.getD c' [])) XC s =
      ∑ i ∈ Finset.range N, X s i * ent 11 10 (Jcols.getD c' 0) i := by
    intro s hs
    rw [lincomb_getD W 10 N s _ _ hJdl hXlen,
      ← Finset.sum_range (fun i => ((((Jd.getD c' []).getD i 0 : ℕ) : ℤ) - 2 ^ 10) * ent W (W - 1) (XC.getD i 0) s)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hJdig i hi, hXent i hi s hs]
    ring
  have hlinb : ∀ s, s < L → |∑ i ∈ Finset.range N, X s i * ent 11 10 (Jcols.getD c' 0) i| ≤
      (N : ℤ) * (2 ^ 10 * Xb) := by
    intro s hs
    calc |∑ i ∈ Finset.range N, X s i * ent 11 10 (Jcols.getD c' 0) i|
        ≤ ∑ i ∈ Finset.range N, |X s i * ent 11 10 (Jcols.getD c' 0) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range N, 2 ^ 10 * Xb := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          rw [abs_mul, mul_comm]
          exact mul_le_mul (hJabs i hi) (hXb i hi s hs) (abs_nonneg _) (by positivity)
      _ = (N : ℤ) * (2 ^ 10 * Xb) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the `Y` column, entry by entry
  have hY : ∀ s, s < L → ent W (W - 1) (x2ChunkY W L Jd XC c') s =
      ∑ i ∈ Finset.range N, X s i * ent 11 10 (Jcols.getD c' 0) i := by
    intro s hs
    have hsound := natAxpyCheck_sound W L 10 (Jd.getD c' []) XC (x2ChunkY W L Jd XC c') hW2
      (by rw [hJdl, hXlen]) hXlt
      (fun k hk => by rw [hlin k hk]; exact lt_of_le_of_lt (hlinb k hk) hb1)
      (natAxpyCheck_res W L 10 _ _) s hs
    rw [← hsound, hlin s hs]
  -- the projection: slots of `Y` against the image rows of the chunk
  have hO := slotCheck_int W L r JR (x2ChunkY W L Jd XC c') ((x2ChunkO W r L Jd XC JR).getD c' 0) hW2 hJRlen
    hJRlt (by
      intro k hk
      calc |∑ a : Fin L, ent W (W - 1) (x2ChunkY W L Jd XC c') a * ent W (W - 1) (JR.getD a 0) k|
          ≤ ∑ a : Fin L, |ent W (W - 1) (x2ChunkY W L Jd XC c') a * ent W (W - 1) (JR.getD a 0) k| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin L, (N : ℤ) * (2 ^ 10 * Xb) * 2 ^ 10 := by
            apply Finset.sum_le_sum
            intro a _
            rw [abs_mul, hY a a.isLt, hJR a a.isLt k hk]
            exact mul_le_mul (hlinb a a.isLt) (hJRb a a.isLt k hk) (abs_nonneg _) (by positivity)
        _ = (L : ℤ) * ((N : ℤ) * (2 ^ 10 * Xb) * 2 ^ 10) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < 2 ^ (W - 1) := hb2)
    (by
      unfold slotCheck
      have e : (x2ChunkO W r L Jd XC JR).getD c' 0 =
          natAxpyRes W r (W - 1) (digs W L (x2ChunkY W L Jd XC c')) JR := by
        unfold x2ChunkO
        exact x2o_getD_map_range r c' _ hc'
      rw [e]
      exact natAxpyCheck_res W r (W - 1) _ _) c hc
  rw [← hO, ← Finset.sum_range (fun a => ent W (W - 1) (x2ChunkY W L Jd XC c') a * ent W (W - 1) (JR.getD a 0) c)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [hY s hs, hJR s hs c hc]
  ring

/-! ### The three integer parts of `x2RawH` (table reads, coordinates as naturals) -/

/-- Part 0: the `S` term plus the `A` placement with the `S` label at site 0. -/
def x2X0 (W : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (x0 x1 x2 y0 y1 y2 : ℕ) : ℤ :=
  ent W (W - 1) (xfTab TS (x2SIdx 0 (x2KeyTypes 0 b 2) x2 y2) (x2SIdx 0 (x2KeyTypes 0 b 1) x1 y1))
      (x2UOff0 (x2KeyTypes 0 b 0) + y0 * x2KeyMult 0 b 0 + x0) +
    sgnZ x1 y1 * sgnZ x2 y2 *
      ent W (W - 1) (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 2) x2 y2) (x2AIdx 0 (x2KeyTypes 0 b 1) x1 y1))
        (x2UOff0 (x2KeyTypes 0 b 0) + y0 * x2KeyMult 0 b 0 + x0)

/-- Part 1: the `A` placement with the `S` label at site 1. -/
def x2X1 (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (x0 x1 x2 y0 y1 y2 : ℕ) : ℤ :=
  sgnZ x0 y0 * sgnZ x2 y2 *
    ent W (W - 1) (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 2) x2 y2) (x2AIdx 0 (x2KeyTypes 0 b 0) x0 y0))
      (x2UOff0 (x2KeyTypes 0 b 1) + y1 * x2KeyMult 0 b 1 + x1)

/-- Part 2: the `A` placement with the `S` label at site 2. -/
def x2X2 (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (x0 x1 x2 y0 y1 y2 : ℕ) : ℤ :=
  sgnZ x0 y0 * sgnZ x1 y1 *
    ent W (W - 1) (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 1) x1 y1) (x2AIdx 0 (x2KeyTypes 0 b 0) x0 y0))
      (x2UOff0 (x2KeyTypes 0 b 2) + y2 * x2KeyMult 0 b 2 + x2)

/-- Flat image index of an ambient point. -/
def x2Fl (b : x2Key 0) (x0 x1 x2 : ℕ) : ℕ := (x0 * x2KeyMult 0 b 1 + x1) * x2KeyMult 0 b 2 + x2

/-- Chunk value of a part: `∑` over the chunk rows of `J[x, c] (X J)[x, c']`, rows enumerated by `(u, v)`
(`pt u v` the ambient point), columns by their flat index `i` (decoded by `x2Dec*`). -/
def x2Dec0 (b : x2Key 0) (i : ℕ) : ℕ := i / (x2KeyMult 0 b 1 * x2KeyMult 0 b 2)
def x2Dec1 (b : x2Key 0) (i : ℕ) : ℕ := (i / x2KeyMult 0 b 2) % x2KeyMult 0 b 1
def x2Dec2 (b : x2Key 0) (i : ℕ) : ℕ := i % x2KeyMult 0 b 2

theorem x2Dec_flat (b : x2Key 0) (y0 y1 y2 : ℕ) (h1 : y1 < x2KeyMult 0 b 1) (h2 : y2 < x2KeyMult 0 b 2) :
    x2Dec0 b (x2Fl b y0 y1 y2) = y0 ∧ x2Dec1 b (x2Fl b y0 y1 y2) = y1 ∧ x2Dec2 b (x2Fl b y0 y1 y2) = y2 := by
  unfold x2Dec0 x2Dec1 x2Dec2 x2Fl
  exact x2o_flat_decode y0 y1 y2 _ _ h1 h2

theorem x2Dec_lt (b : x2Key 0) (i : ℕ) (hi : i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) :
    x2Dec0 b i < x2KeyMult 0 b 0 ∧ x2Dec1 b i < x2KeyMult 0 b 1 ∧ x2Dec2 b i < x2KeyMult 0 b 2 ∧
      x2Fl b (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) = i := by
  have hm2 : 0 < x2KeyMult 0 b 2 := by
    rcases Nat.eq_zero_or_pos (x2KeyMult 0 b 2) with h | h
    · rw [h, mul_zero] at hi; exact absurd hi (Nat.not_lt_zero _)
    · exact h
  have hm1 : 0 < x2KeyMult 0 b 1 := by
    rcases Nat.eq_zero_or_pos (x2KeyMult 0 b 1) with h | h
    · rw [h, mul_zero, zero_mul] at hi; exact absurd hi (Nat.not_lt_zero _)
    · exact h
  unfold x2Dec0 x2Dec1 x2Dec2 x2Fl
  refine ⟨?_, Nat.mod_lt _ hm1, Nat.mod_lt _ hm2, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hm1 hm2)]
    calc i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 := hi
      _ = x2KeyMult 0 b 0 * (x2KeyMult 0 b 1 * x2KeyMult 0 b 2) := by ring
  · have e1 : i / (x2KeyMult 0 b 1 * x2KeyMult 0 b 2) = i / x2KeyMult 0 b 2 / x2KeyMult 0 b 1 := by
      rw [Nat.div_div_eq_div_mul, mul_comm]
    rw [e1]
    have e2 := Nat.div_add_mod (i / x2KeyMult 0 b 2) (x2KeyMult 0 b 1)
    have e3 := Nat.div_add_mod i (x2KeyMult 0 b 2)
    calc (i / x2KeyMult 0 b 2 / x2KeyMult 0 b 1 * x2KeyMult 0 b 1 + i / x2KeyMult 0 b 2 % x2KeyMult 0 b 1) *
          x2KeyMult 0 b 2 + i % x2KeyMult 0 b 2
        = (x2KeyMult 0 b 1 * (i / x2KeyMult 0 b 2 / x2KeyMult 0 b 1) + i / x2KeyMult 0 b 2 % x2KeyMult 0 b 1) *
            x2KeyMult 0 b 2 + i % x2KeyMult 0 b 2 := by ring
      _ = i / x2KeyMult 0 b 2 * x2KeyMult 0 b 2 + i % x2KeyMult 0 b 2 := by rw [e2]
      _ = x2KeyMult 0 b 2 * (i / x2KeyMult 0 b 2) + i % x2KeyMult 0 b 2 := by ring
      _ = i := e3


/-! ### Extraction helpers -/

theorem xf_all3 {P : ℕ → ℕ → ℕ → Bool} {n1 n2 n3 : ℕ}
    (h : ((List.range n1).all fun i => (List.range n2).all fun j => (List.range n3).all fun k => P i j k) = true)
    (i j k : ℕ) (hi : i < n1) (hj : j < n2) (hk : k < n3) : P i j k = true := by
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  exact List.all_eq_true.mp h2 k (List.mem_range.mpr hk)

theorem xf_ent_runOf_comb (W m u s : ℕ) (F : ℕ) (hs : s < m) :
    ent W (W - 1) (runOf W m u F) s = ent W (W - 1) F (u + s) := ent_runOf W m u F s hs

theorem xf_runComb_zero (W m r₁ r₂ : ℕ) : runComb W m r₁ r₂ 0 = r₁ := by
  simp [runComb]

theorem xf_mod_div (s m n : ℕ) (hs : s < n * m) : s / m < n ∧ s % m < m ∧ s / m * m + s % m = s := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hs; exact absurd hs (Nat.not_lt_zero _)
    · exact h
  refine ⟨?_, Nat.mod_lt _ hm, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hm]; exact hs
  · have := Nat.div_add_mod s m
    rw [mul_comm] at this
    exact this

theorem xf_x2Fl_lt (b : x2Key 0) (x0 x1 x2 : ℕ) (h0 : x0 < x2KeyMult 0 b 0) (h1 : x1 < x2KeyMult 0 b 1)
    (h2 : x2 < x2KeyMult 0 b 2) : x2Fl b x0 x1 x2 < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 := by
  unfold x2Fl
  exact x2o_lt_mul _ x2 _ _ (x2o_lt_mul x0 x1 _ _ h0 h1) h2

/-- Image rows: bound, range, entries. -/
theorem jRowF_lt (W : ℕ) (Jcols : List ℕ) (p : ℕ) (hW : 12 ≤ W) : jRowF W Jcols p < 2 ^ (W * Jcols.length) := by
  rw [jRowF_eq]; exact jRowOf_lt W _ Jcols p hW

theorem jRowF_ent (W : ℕ) (Jcols : List ℕ) (p c : ℕ) (hW : 12 ≤ W) (hc : c < Jcols.length) :
    ent W (W - 1) (jRowF W Jcols p) c = ent 11 10 (Jcols.getD c 0) p := by
  rw [jRowF_eq]; exact jRowOf_ent W _ Jcols p c hW hc

/-- The columns of a chunk: flat-index lookup in a nested map over `(y₀, y₁, y₂)`. -/
theorem xf_nested_getD (m0 m1 m2 : ℕ) (col : ℕ → ℕ → ℕ → ℕ) (y0 y1 y2 : ℕ) (hy0 : y0 < m0) (hy1 : y1 < m1)
    (hy2 : y2 < m2) :
    ((List.range m0).flatMap fun y0 => (List.range m1).flatMap fun y1 =>
        (List.range m2).map fun y2 => col y0 y1 y2).getD ((y0 * m1 + y1) * m2 + y2) 0 = col y0 y1 y2 := by
  have hin : ∀ y0, ((List.range m1).flatMap fun y1 => (List.range m2).map fun y2 => col y0 y1 y2).length =
      m1 * m2 := fun y0 =>
    xf_length_flatMap_range m2 (fun y1 => (List.range m2).map fun y2 => col y0 y1 y2) (fun _ => by simp) m1
  rw [show (y0 * m1 + y1) * m2 + y2 = y0 * (m1 * m2) + (y1 * m2 + y2) by ring,
    xf_getD_flatMap_range (m1 * m2)
      (fun y0 => (List.range m1).flatMap fun y1 => (List.range m2).map fun y2 => col y0 y1 y2) hin m0 y0 _ hy0
      (x2o_lt_mul y1 y2 m2 m1 hy1 hy2)]
  rw [xf_getD_flatMap_range m2 (fun y1 => (List.range m2).map fun y2 => col y0 y1 y2) (fun _ => by simp) m1 y1 y2
    hy1 hy2]
  exact x2o_getD_map_range m2 y2 _ hy2

theorem xf_nested_length (m0 m1 m2 : ℕ) (col : ℕ → ℕ → ℕ → ℕ) :
    ((List.range m0).flatMap fun y0 => (List.range m1).flatMap fun y1 =>
        (List.range m2).map fun y2 => col y0 y1 y2).length = m0 * m1 * m2 := by
  rw [xf_length_flatMap_range (m1 * m2)
    (fun y0 => (List.range m1).flatMap fun y1 => (List.range m2).map fun y2 => col y0 y1 y2)
    (fun y0 => xf_length_flatMap_range m2 (fun y1 => (List.range m2).map fun y2 => col y0 y1 y2)
      (fun _ => by simp) m1) m0]
  ring

theorem xf_nested_mem (m0 m1 m2 : ℕ) (col : ℕ → ℕ → ℕ → ℕ) (P : ℕ → Prop) (h : ∀ y0 y1 y2, P (col y0 y1 y2)) :
    ∀ z ∈ ((List.range m0).flatMap fun y0 => (List.range m1).flatMap fun y1 =>
        (List.range m2).map fun y2 => col y0 y1 y2), P z := by
  intro z hz
  rw [List.mem_flatMap] at hz
  obtain ⟨y0, _, hz⟩ := hz
  rw [List.mem_flatMap] at hz
  obtain ⟨y1, _, hz⟩ := hz
  obtain ⟨y2, _, rfl⟩ := List.mem_map.mp hz
  exact h y0 y1 y2

/-- Rows of a chunk: lookup in a nested map over `(u, v)`. -/
theorem xf_rows_getD (n1 n2 : ℕ) (row : ℕ → ℕ → ℕ) (s : ℕ) (hs : s < n1 * n2) :
    ((List.range n1).flatMap fun u => (List.range n2).map fun v => row u v).getD s 0 = row (s / n2) (s % n2) := by
  obtain ⟨h1, h2, h3⟩ := xf_mod_div s n2 n1 hs
  conv_lhs => rw [← h3]
  rw [xf_getD_flatMap_range n2 (fun u => (List.range n2).map fun v => row u v) (fun _ => by simp) n1 _ _ h1 h2]
  exact x2o_getD_map_range n2 _ _ h2

theorem xf_rows_length (n1 n2 : ℕ) (row : ℕ → ℕ → ℕ) :
    ((List.range n1).flatMap fun u => (List.range n2).map fun v => row u v).length = n1 * n2 :=
  xf_length_flatMap_range n2 (fun u => (List.range n2).map fun v => row u v) (fun _ => by simp) n1

theorem xf_rows_mem (n1 n2 : ℕ) (row : ℕ → ℕ → ℕ) (P : ℕ → Prop) (h : ∀ u v, P (row u v)) :
    ∀ z ∈ ((List.range n1).flatMap fun u => (List.range n2).map fun v => row u v), P z := by
  intro z hz
  rw [List.mem_flatMap] at hz
  obtain ⟨u, _, hz⟩ := hz
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
  exact h u v

/-- A column made of runs: slot `q m + s`. -/
theorem xf_col_ent (W m : ℕ) (G : List ℕ) (off q s : ℕ) (hq : q < G.length) (hs : s < m) :
    ent W (W - 1) (concatFibers W m (G.map (runOf W m off))) (q * m + s) = ent W (W - 1) (G.getD q 0) (off + s) := by
  have hlt : ∀ r ∈ G.map (runOf W m off), r < 2 ^ (W * m) := by
    intro r hr
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hr
    exact runOf_lt _ _ _ _
  rw [ent_concat_runs W m _ hlt q s (by simpa using hq) hs, xf_getD_map_zero _ (runOf_zero W m off),
    ent_runOf W m off _ s hs]

theorem xf_col_lt (W m : ℕ) (G : List ℕ) (off n : ℕ) (hG : G.length = n) :
    concatFibers W m (G.map (runOf W m off)) < 2 ^ (W * (n * m)) := by
  have hlt : ∀ r ∈ G.map (runOf W m off), r < 2 ^ (W * m) := by
    intro r hr
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hr
    exact runOf_lt _ _ _ _
  have h := concatFibers_lt W m _ hlt
  rw [List.length_map, hG] at h
  rw [show W * (n * m) = W * m * n by ring]
  exact h

/-! ### Part 0, chunk `x₂ = a`: rows `(x₀, x₁, a)`, slot `x₁ m₀ + x₀` -/

/-- S triangle of part 0 at `y₂`: table row `S(t₂, a, y₂)`, type-`t₁` labels, type-`t₀` slots. -/
def x2F0RS (W : ℕ) (b : x2Key 0) (TS : List (List ℕ)) (a y2 : ℕ) : List (List ℕ) :=
  triSOf W (x2KeyMult 0 b 0 * x2KeyMult 0 b 0) (x2UOff0 (x2KeyTypes 0 b 0)) (x2KeyTypes 0 b 1) TS
    (x2SIdx 0 (x2KeyTypes 0 b 2) a y2)

/-- A triangle of part 0 at `y₂`: table row `A(t₂, a, y₂)`, type-`t₁` labels, type-`t₀` slots. -/
def x2F0RA (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a y2 : ℕ) : List (List ℕ) :=
  triAOf W (x2KeyMult 0 b 0 * x2KeyMult 0 b 0) (x2UOff0 (x2KeyTypes 0 b 0)) (x2KeyTypes 0 b 1) TA
    (x2AIdx 0 (x2KeyTypes 0 b 2) a y2)

/-- The combined sub-fibers of part 0 for the columns `(·, y₁, y₂)`, one per `x₁`. -/
def x2F0G (W : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (a y2 y1 : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 1)).map fun x1 =>
    runComb W (x2KeyMult 0 b 0 * x2KeyMult 0 b 0) (triS (x2F0RS W b TS a y2) x1 y1)
      (triA (x2F0RA W b TA a y2) x1 y1) (sgnZ x1 y1 * sgnZ a y2)

/-- Column `(y₀, y₁, y₂)` of the part-0 chunk `a`. -/
def x2F0Col (W : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (a y0 y1 y2 : ℕ) : ℕ :=
  concatFibers W (x2KeyMult 0 b 0)
    ((x2F0G W b TS TA a y2 y1).map (runOf W (x2KeyMult 0 b 0) (y0 * x2KeyMult 0 b 0)))

/-- The columns of the part-0 chunk `a`, in flat order. -/
def x2F0XC (W : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (a : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).flatMap fun y0 => (List.range (x2KeyMult 0 b 1)).flatMap fun y1 =>
    (List.range (x2KeyMult 0 b 2)).map fun y2 => x2F0Col W b TS TA a y0 y1 y2

/-- Image rows of the part-0 chunk `a`. -/
def x2F0JR (W : ℕ) (b : x2Key 0) (Jcols : List ℕ) (a : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 1)).flatMap fun x1 => (List.range (x2KeyMult 0 b 0)).map fun x0 =>
    jRowF W Jcols (x2Fl b x0 x1 a)

/-- Slot bounds of the sub-fibers read by the part-0 chunk `a`. -/
def x2F0Bnd (W bF : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (a : ℕ) : Bool :=
  (List.range (x2KeyMult 0 b 2)).all fun y2 => (List.range (x2KeyMult 0 b 1)).all fun y1 =>
    (List.range (x2KeyMult 0 b 1)).all fun x1 =>
      slotBoundCheck W bF (x2KeyMult 0 b 0 * x2KeyMult 0 b 0) (triS (x2F0RS W b TS a y2) x1 y1) &&
        (x1 == y1 || a == y2 ||
          slotBoundCheck W bF (x2KeyMult 0 b 0 * x2KeyMult 0 b 0) (triA (x2F0RA W b TA a y2) x1 y1))

/-- The kernel check of the part-0 chunk `a` against a literal. -/
noncomputable def x2F0OK (W bF : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (Jd : List (List ℕ))
    (Jcols : List ℕ) (a : ℕ) (lit : List ℕ) : Bool :=
  x2F0Bnd W bF b TS TA a &&
    decide (x2ChunkO W (x2KeySize 0 b) (x2KeyMult 0 b 1 * x2KeyMult 0 b 0) Jd (x2F0XC W b TS TA a)
      (x2F0JR W b Jcols a) = lit)

/-- Build-time candidate for the part-0 chunk `a`. -/
def x2F0OC (W : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ) (a : ℕ) :
    List ℕ :=
  x2ChunkOC W (x2KeySize 0 b) (x2KeyMult 0 b 1 * x2KeyMult 0 b 0) Jd (x2F0XC W b TS TA a) (x2F0JR W b Jcols a)

theorem x2F0XC_ent (W bF : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (a : ℕ) (hW : 2 ≤ W) (hbF : bF + 3 ≤ W)
    (ha : a < x2KeyMult 0 b 2) (hbnd : x2F0Bnd W bF b TS TA a = true)
    (y0 y1 y2 x0 x1 : ℕ) (hy0 : y0 < x2KeyMult 0 b 0) (hy1 : y1 < x2KeyMult 0 b 1) (hy2 : y2 < x2KeyMult 0 b 2)
    (hx0 : x0 < x2KeyMult 0 b 0) (hx1 : x1 < x2KeyMult 0 b 1) :
    ent W (W - 1) ((x2F0XC W b TS TA a).getD (x2Fl b y0 y1 y2) 0) (x1 * x2KeyMult 0 b 0 + x0) =
        x2X0 W b TS TA x0 x1 a y0 y1 y2 ∧
      |x2X0 W b TS TA x0 x1 a y0 y1 y2| ≤ 2 ^ (bF + 1) := by
  have hW1 : 1 ≤ W := by omega
  have hb2W : bF + 2 ≤ W := by omega
  have hs : y0 * x2KeyMult 0 b 0 + x0 < x2KeyMult 0 b 0 * x2KeyMult 0 b 0 := x2o_lt_mul y0 x0 _ _ hy0 hx0
  -- the bound checks at this entry
  unfold x2F0Bnd at hbnd
  have hc := xf_all3 hbnd y2 y1 x1 hy2 hy1 hx1
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨hcS, hcA⟩ := hc
  have hbS := (slotBoundCheck_sound W bF _ _ hb2W hcS).2
  -- the S sub-fiber
  have hS : triS (x2F0RS W b TS a y2) x1 y1 = runOf W (x2KeyMult 0 b 0 * x2KeyMult 0 b 0)
      (x2UOff0 (x2KeyTypes 0 b 0)) (xfTab TS (x2SIdx 0 (x2KeyTypes 0 b 2) a y2) (x2SIdx 0 (x2KeyTypes 0 b 1) x1 y1)) :=
    triS_eq _ _ _ _ _ _ _ _ hx1 hy1
  -- the column entry is an entry of the combined sub-fiber
  have hcol : ent W (W - 1) ((x2F0XC W b TS TA a).getD (x2Fl b y0 y1 y2) 0) (x1 * x2KeyMult 0 b 0 + x0) =
      ent W (W - 1) (runComb W (x2KeyMult 0 b 0 * x2KeyMult 0 b 0) (triS (x2F0RS W b TS a y2) x1 y1)
        (triA (x2F0RA W b TA a y2) x1 y1) (sgnZ x1 y1 * sgnZ a y2)) (y0 * x2KeyMult 0 b 0 + x0) := by
    have hq : x1 < (x2F0G W b TS TA a y2 y1).length := by simp [x2F0G]; exact hx1
    unfold x2F0XC x2Fl
    rw [xf_nested_getD _ _ _ (fun y0 y1 y2 => x2F0Col W b TS TA a y0 y1 y2) y0 y1 y2 hy0 hy1 hy2]
    unfold x2F0Col
    rw [xf_col_ent W (x2KeyMult 0 b 0) (x2F0G W b TS TA a y2 y1) (y0 * x2KeyMult 0 b 0) x1 x0 hq hx0]
    unfold x2F0G
    rw [x2o_getD_map_range _ x1 _ hx1]
  rw [hcol]
  by_cases he : sgnZ x1 y1 * sgnZ a y2 = 0
  · rw [he, xf_runComb_zero, hS, ent_runOf _ _ _ _ _ hs]
    have hX : x2X0 W b TS TA x0 x1 a y0 y1 y2 = ent W (W - 1)
        (xfTab TS (x2SIdx 0 (x2KeyTypes 0 b 2) a y2) (x2SIdx 0 (x2KeyTypes 0 b 1) x1 y1))
        (x2UOff0 (x2KeyTypes 0 b 0) + (y0 * x2KeyMult 0 b 0 + x0)) := by
      unfold x2X0
      rw [he, zero_mul, add_zero, Nat.add_assoc]
    rw [hX]
    refine ⟨rfl, ?_⟩
    have h1 := hbS _ hs
    rw [hS, ent_runOf _ _ _ _ _ hs] at h1
    have hp : (2 : ℤ) ^ bF ≤ 2 ^ (bF + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact le_trans h1 hp
  · have hne := x2o_ne_of_sgn x1 y1 a y2 he
    have hcA' : slotBoundCheck W bF (x2KeyMult 0 b 0 * x2KeyMult 0 b 0) (triA (x2F0RA W b TA a y2) x1 y1) = true := by
      rcases hcA with (h | h) | h
      · exact absurd h hne.1
      · exact absurd h hne.2
      · exact h
    have hbA := (slotBoundCheck_sound W bF _ _ hb2W hcA').2
    have hA : triA (x2F0RA W b TA a y2) x1 y1 = runOf W (x2KeyMult 0 b 0 * x2KeyMult 0 b 0)
        (x2UOff0 (x2KeyTypes 0 b 0)) (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 2) a y2) (x2AIdx 0 (x2KeyTypes 0 b 1) x1 y1)) :=
      triA_eq _ _ _ _ _ _ _ _ hx1 hy1 hne.1
    have hb := fun s (hs' : s < x2KeyMult 0 b 0 * x2KeyMult 0 b 0) =>
      x2o_bound2 _ _ (sgnZ x1 y1 * sgnZ a y2) bF W hbF (hbS s hs') (abs_sgnZ_mul_le x1 y1 a y2) (fun _ => hbA s hs')
    rw [runComb_ent W _ _ _ _ hW (sgnZ_mul_cases _ _ _ _) (by rw [hS]; exact runOf_lt _ _ _ _)
      (by rw [hA]; exact runOf_lt _ _ _ _) (fun s hs' => (hb s hs').2) _ hs]
    have hval : ent W (W - 1) (triS (x2F0RS W b TS a y2) x1 y1) (y0 * x2KeyMult 0 b 0 + x0) +
        sgnZ x1 y1 * sgnZ a y2 * ent W (W - 1) (triA (x2F0RA W b TA a y2) x1 y1) (y0 * x2KeyMult 0 b 0 + x0) =
        x2X0 W b TS TA x0 x1 a y0 y1 y2 := by
      rw [hS, hA, ent_runOf _ _ _ _ _ hs, ent_runOf _ _ _ _ _ hs]
      unfold x2X0
      rw [Nat.add_assoc]
    refine ⟨hval, ?_⟩
    rw [← hval]
    exact (hb _ hs).1

theorem x2F0OK_sound (W bF : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ)
    (a : ℕ) (lit : List ℕ) (hW : 12 ≤ W) (hbF : bF + 3 ≤ W) (ha : a < x2KeyMult 0 b 2)
    (hJc : Jcols.length = x2KeySize 0 b)
    (hJd : ∀ c < x2KeySize 0 b,
      Jd.getD c [] = digs 11 (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (Jcols.getD c 0))
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) < 2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 1 * x2KeyMult 0 b 0 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1))
    (hok : x2F0OK W bF b TS TA Jd Jcols a lit = true) (c c' : ℕ) (hc : c < x2KeySize 0 b)
    (hc' : c' < x2KeySize 0 b) :
    ent W (W - 1) (lit.getD c' 0) c =
      ∑ x1 ∈ Finset.range (x2KeyMult 0 b 1), ∑ x0 ∈ Finset.range (x2KeyMult 0 b 0),
        ent 11 10 (Jcols.getD c 0) (x2Fl b x0 x1 a) *
          ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
            x2X0 W b TS TA x0 x1 a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i := by
  have hW2 : 2 ≤ W := by omega
  unfold x2F0OK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hbnd, hlit⟩ := hok
  rw [← hlit]
  have hent : ∀ i, i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 → ∀ s,
      s < x2KeyMult 0 b 1 * x2KeyMult 0 b 0 →
      ent W (W - 1) ((x2F0XC W b TS TA a).getD i 0) s =
          x2X0 W b TS TA (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) ∧
        |x2X0 W b TS TA (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i)| ≤
          2 ^ (bF + 1) := by
    intro i hi s hs
    obtain ⟨hd0, hd1, hd2, hfl⟩ := x2Dec_lt b i hi
    obtain ⟨hq, hr, hqr⟩ := xf_mod_div s (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) hs
    have h := x2F0XC_ent W bF b TS TA a hW2 hbF ha hbnd (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) (s % x2KeyMult 0 b 0)
      (s / x2KeyMult 0 b 0) hd0 hd1 hd2 hr hq
    rw [hfl, hqr] at h
    exact h
  rw [x2ChunkProj W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b)
      (x2KeyMult 0 b 1 * x2KeyMult 0 b 0) Jcols Jd (x2F0XC W b TS TA a) (x2F0JR W b Jcols a)
      (fun s i => x2X0 W b TS TA (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i))
      (fun s c => ent 11 10 (Jcols.getD c 0) (x2Fl b (s % x2KeyMult 0 b 0) (s / x2KeyMult 0 b 0) a))
      (2 ^ (bF + 1)) hW (by positivity) hJd
      (by unfold x2F0XC; exact xf_nested_length _ _ _ _)
      (by
        unfold x2F0XC
        exact xf_nested_mem _ _ _ (fun y0 y1 y2 => x2F0Col W b TS TA a y0 y1 y2)
          (fun z => z < 2 ^ (W * (x2KeyMult 0 b 1 * x2KeyMult 0 b 0)))
          (fun y0 y1 y2 => xf_col_lt W (x2KeyMult 0 b 0) (x2F0G W b TS TA a y2 y1) (y0 * x2KeyMult 0 b 0)
            (x2KeyMult 0 b 1) (by simp [x2F0G])))
      (fun i hi s hs => (hent i hi s hs).1) (fun i hi s hs => (hent i hi s hs).2)
      (by unfold x2F0JR; exact xf_rows_length _ _ _)
      (by
        unfold x2F0JR
        exact xf_rows_mem _ _ (fun x1 x0 => jRowF W Jcols (x2Fl b x0 x1 a)) (fun z => z < 2 ^ (W * x2KeySize 0 b))
          (fun u v => by (try beta_reduce); rw [← hJc]; exact jRowF_lt W Jcols _ hW))
      (by
        intro s hs c hc
        unfold x2F0JR
        rw [xf_rows_getD _ _ (fun x1 x0 => jRowF W Jcols (x2Fl b x0 x1 a)) s hs]
        exact jRowF_ent W Jcols _ c hW (by rw [hJc]; exact hc))
      (fun s _ c _ => ent11_abs_le _ _) hb1 hb2 c c' hc hc']
  rw [xf_sum_range_mul _ (x2KeyMult 0 b 0) (x2KeyMult 0 b 1)]
  apply Finset.sum_congr rfl
  intro x1 hx1
  apply Finset.sum_congr rfl
  intro x0 hx0
  rw [Finset.mem_range] at hx0
  obtain ⟨hdv, hmd⟩ := x2o_divmod x1 x0 (x2KeyMult 0 b 0) hx0
  simp only [hdv, hmd]

/-! ### Part 1, chunk `x₂ = a`: rows `(x₀, x₁, a)`, slot `x₀ m₁ + x₁` -/

/-- A triangle of part 1 at `y₂`: table row `A(t₂, a, y₂)`, type-`t₀` labels, type-`t₁` slots. -/
def x2F1RA (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a y2 : ℕ) : List (List ℕ) :=
  triAOf W (x2KeyMult 0 b 1 * x2KeyMult 0 b 1) (x2UOff0 (x2KeyTypes 0 b 1)) (x2KeyTypes 0 b 0) TA
    (x2AIdx 0 (x2KeyTypes 0 b 2) a y2)

/-- The signed sub-fibers of part 1 for the columns `(y₀, ·, y₂)`, one per `x₀`. -/
def x2F1G (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a y2 y0 : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).map fun x0 =>
    runComb W (x2KeyMult 0 b 1 * x2KeyMult 0 b 1) (offset W (W - 1) (x2KeyMult 0 b 1 * x2KeyMult 0 b 1))
      (triA (x2F1RA W b TA a y2) x0 y0) (sgnZ x0 y0 * sgnZ a y2)

def x2F1Col (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a y0 y1 y2 : ℕ) : ℕ :=
  concatFibers W (x2KeyMult 0 b 1)
    ((x2F1G W b TA a y2 y0).map (runOf W (x2KeyMult 0 b 1) (y1 * x2KeyMult 0 b 1)))

def x2F1XC (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).flatMap fun y0 => (List.range (x2KeyMult 0 b 1)).flatMap fun y1 =>
    (List.range (x2KeyMult 0 b 2)).map fun y2 => x2F1Col W b TA a y0 y1 y2

def x2F1JR (W : ℕ) (b : x2Key 0) (Jcols : List ℕ) (a : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).flatMap fun x0 => (List.range (x2KeyMult 0 b 1)).map fun x1 =>
    jRowF W Jcols (x2Fl b x0 x1 a)

def x2F1Bnd (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a : ℕ) : Bool :=
  (List.range (x2KeyMult 0 b 2)).all fun y2 => (List.range (x2KeyMult 0 b 0)).all fun y0 =>
    (List.range (x2KeyMult 0 b 0)).all fun x0 =>
      (x0 == y0 || a == y2 ||
        slotBoundCheck W bF (x2KeyMult 0 b 1 * x2KeyMult 0 b 1) (triA (x2F1RA W b TA a y2) x0 y0))

noncomputable def x2F1OK (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ)
    (a : ℕ) (lit : List ℕ) : Bool :=
  x2F1Bnd W bF b TA a &&
    decide (x2ChunkO W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1) Jd (x2F1XC W b TA a)
      (x2F1JR W b Jcols a) = lit)

def x2F1OC (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ) (a : ℕ) : List ℕ :=
  x2ChunkOC W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 1) Jd (x2F1XC W b TA a) (x2F1JR W b Jcols a)

/-- Entry of a signed run `0 + e A` (shared by parts 1 and 2). -/
theorem xf_signed_ent (W bF m : ℕ) (R : List (List ℕ)) (x y : ℕ) (e : ℤ) (F : ℕ) (u s : ℕ)
    (hW : 2 ≤ W) (hbF : bF + 3 ≤ W) (hs : s < m * m) (he : e = 0 ∨ e = 1 ∨ e = -1)
    (hA : e ≠ 0 → triA R x y = runOf W (m * m) u F)
    (hbA : e ≠ 0 → slotBoundCheck W bF (m * m) (triA R x y) = true) :
    ent W (W - 1) (runComb W (m * m) (offset W (W - 1) (m * m)) (triA R x y) e) s = e * ent W (W - 1) F (u + s) ∧
      |e * ent W (W - 1) F (u + s)| ≤ 2 ^ (bF + 1) := by
  have hW1 : 1 ≤ W := by omega
  have hb2W : bF + 2 ≤ W := by omega
  by_cases h0 : e = 0
  · subst h0
    rw [xf_runComb_zero, x2o_ent_offset W _ s hW1 hs, zero_mul]
    exact ⟨rfl, by rw [abs_zero]; positivity⟩
  · have hbnd := (slotBoundCheck_sound W bF _ _ hb2W (hbA h0)).2
    have hb : ∀ k < m * m, |ent W (W - 1) (offset W (W - 1) (m * m)) k + e * ent W (W - 1) (triA R x y) k| ≤
        2 ^ (bF + 1) ∧ |ent W (W - 1) (offset W (W - 1) (m * m)) k + e * ent W (W - 1) (triA R x y) k| <
          2 ^ (W - 1) := by
      intro k hk
      rw [x2o_ent_offset W _ k hW1 hk]
      have habs : |e| ≤ 1 := by rcases he with h | h | h <;> rw [h] <;> norm_num
      exact x2o_bound2 0 _ e bF W hbF (by rw [abs_zero]; positivity) habs (fun _ => hbnd k hk)
    rw [runComb_ent W _ _ _ _ hW he (x2o_offset_lt W _ hW1) (by rw [hA h0]; exact runOf_lt _ _ _ _)
      (fun k hk => (hb k hk).2) s hs]
    have hv : ent W (W - 1) (offset W (W - 1) (m * m)) s + e * ent W (W - 1) (triA R x y) s =
        e * ent W (W - 1) F (u + s) := by
      rw [x2o_ent_offset W _ s hW1 hs, zero_add, hA h0, ent_runOf _ _ _ _ _ hs]
    refine ⟨hv, ?_⟩
    rw [← hv]
    exact (hb s hs).1

theorem x2F1XC_ent (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a : ℕ) (hW : 2 ≤ W) (hbF : bF + 3 ≤ W)
    (ha : a < x2KeyMult 0 b 2) (hbnd : x2F1Bnd W bF b TA a = true)
    (y0 y1 y2 x0 x1 : ℕ) (hy0 : y0 < x2KeyMult 0 b 0) (hy1 : y1 < x2KeyMult 0 b 1) (hy2 : y2 < x2KeyMult 0 b 2)
    (hx0 : x0 < x2KeyMult 0 b 0) (hx1 : x1 < x2KeyMult 0 b 1) :
    ent W (W - 1) ((x2F1XC W b TA a).getD (x2Fl b y0 y1 y2) 0) (x0 * x2KeyMult 0 b 1 + x1) =
        x2X1 W b TA x0 x1 a y0 y1 y2 ∧
      |x2X1 W b TA x0 x1 a y0 y1 y2| ≤ 2 ^ (bF + 1) := by
  have hs : y1 * x2KeyMult 0 b 1 + x1 < x2KeyMult 0 b 1 * x2KeyMult 0 b 1 := x2o_lt_mul y1 x1 _ _ hy1 hx1
  unfold x2F1Bnd at hbnd
  have hc := xf_all3 hbnd y2 y0 x0 hy2 hy0 hx0
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  have hq : x0 < (x2F1G W b TA a y2 y0).length := by simp [x2F1G]; exact hx0
  have hcol : ent W (W - 1) ((x2F1XC W b TA a).getD (x2Fl b y0 y1 y2) 0) (x0 * x2KeyMult 0 b 1 + x1) =
      ent W (W - 1) (runComb W (x2KeyMult 0 b 1 * x2KeyMult 0 b 1)
        (offset W (W - 1) (x2KeyMult 0 b 1 * x2KeyMult 0 b 1)) (triA (x2F1RA W b TA a y2) x0 y0)
        (sgnZ x0 y0 * sgnZ a y2)) (y1 * x2KeyMult 0 b 1 + x1) := by
    unfold x2F1XC x2Fl
    rw [xf_nested_getD _ _ _ (fun y0 y1 y2 => x2F1Col W b TA a y0 y1 y2) y0 y1 y2 hy0 hy1 hy2]
    unfold x2F1Col
    rw [xf_col_ent W (x2KeyMult 0 b 1) (x2F1G W b TA a y2 y0) (y1 * x2KeyMult 0 b 1) x0 x1 hq hx1]
    unfold x2F1G
    rw [x2o_getD_map_range _ x0 _ hx0]
  rw [hcol]
  have h := xf_signed_ent W bF (x2KeyMult 0 b 1) (x2F1RA W b TA a y2) x0 y0 (sgnZ x0 y0 * sgnZ a y2)
    (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 2) a y2) (x2AIdx 0 (x2KeyTypes 0 b 0) x0 y0)) (x2UOff0 (x2KeyTypes 0 b 1))
    (y1 * x2KeyMult 0 b 1 + x1) hW hbF hs (sgnZ_mul_cases _ _ _ _)
    (fun he => triA_eq _ _ _ _ _ _ _ _ hx0 hy0 (x2o_ne_of_sgn _ _ _ _ he).1)
    (fun he => by
      have hne := x2o_ne_of_sgn _ _ _ _ he
      rcases hc with (h | h) | h
      · exact absurd h hne.1
      · exact absurd h hne.2
      · exact h)
  have hX : x2X1 W b TA x0 x1 a y0 y1 y2 = sgnZ x0 y0 * sgnZ a y2 *
      ent W (W - 1) (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 2) a y2) (x2AIdx 0 (x2KeyTypes 0 b 0) x0 y0))
        (x2UOff0 (x2KeyTypes 0 b 1) + (y1 * x2KeyMult 0 b 1 + x1)) := by
    unfold x2X1
    rw [Nat.add_assoc]
  rw [hX]
  exact h

theorem x2F1OK_sound (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ)
    (a : ℕ) (lit : List ℕ) (hW : 12 ≤ W) (hbF : bF + 3 ≤ W) (ha : a < x2KeyMult 0 b 2)
    (hJc : Jcols.length = x2KeySize 0 b)
    (hJd : ∀ c < x2KeySize 0 b,
      Jd.getD c [] = digs 11 (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (Jcols.getD c 0))
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) < 2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1))
    (hok : x2F1OK W bF b TA Jd Jcols a lit = true) (c c' : ℕ) (hc : c < x2KeySize 0 b)
    (hc' : c' < x2KeySize 0 b) :
    ent W (W - 1) (lit.getD c' 0) c =
      ∑ x0 ∈ Finset.range (x2KeyMult 0 b 0), ∑ x1 ∈ Finset.range (x2KeyMult 0 b 1),
        ent 11 10 (Jcols.getD c 0) (x2Fl b x0 x1 a) *
          ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
            x2X1 W b TA x0 x1 a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i := by
  have hW2 : 2 ≤ W := by omega
  unfold x2F1OK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hbnd, hlit⟩ := hok
  rw [← hlit]
  have hent : ∀ i, i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 → ∀ s,
      s < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 →
      ent W (W - 1) ((x2F1XC W b TA a).getD i 0) s =
          x2X1 W b TA (s / x2KeyMult 0 b 1) (s % x2KeyMult 0 b 1) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) ∧
        |x2X1 W b TA (s / x2KeyMult 0 b 1) (s % x2KeyMult 0 b 1) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i)| ≤
          2 ^ (bF + 1) := by
    intro i hi s hs
    obtain ⟨hd0, hd1, hd2, hfl⟩ := x2Dec_lt b i hi
    obtain ⟨hq, hr, hqr⟩ := xf_mod_div s (x2KeyMult 0 b 1) (x2KeyMult 0 b 0) hs
    have h := x2F1XC_ent W bF b TA a hW2 hbF ha hbnd (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) (s / x2KeyMult 0 b 1)
      (s % x2KeyMult 0 b 1) hd0 hd1 hd2 hq hr
    rw [hfl, hqr] at h
    exact h
  rw [x2ChunkProj W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b)
      (x2KeyMult 0 b 0 * x2KeyMult 0 b 1) Jcols Jd (x2F1XC W b TA a) (x2F1JR W b Jcols a)
      (fun s i => x2X1 W b TA (s / x2KeyMult 0 b 1) (s % x2KeyMult 0 b 1) a (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i))
      (fun s c => ent 11 10 (Jcols.getD c 0) (x2Fl b (s / x2KeyMult 0 b 1) (s % x2KeyMult 0 b 1) a))
      (2 ^ (bF + 1)) hW (by positivity) hJd
      (by unfold x2F1XC; exact xf_nested_length _ _ _ _)
      (by
        unfold x2F1XC
        exact xf_nested_mem _ _ _ (fun y0 y1 y2 => x2F1Col W b TA a y0 y1 y2)
          (fun z => z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 1)))
          (fun y0 y1 y2 => xf_col_lt W (x2KeyMult 0 b 1) (x2F1G W b TA a y2 y0) (y1 * x2KeyMult 0 b 1)
            (x2KeyMult 0 b 0) (by simp [x2F1G])))
      (fun i hi s hs => (hent i hi s hs).1) (fun i hi s hs => (hent i hi s hs).2)
      (by unfold x2F1JR; exact xf_rows_length _ _ _)
      (by
        unfold x2F1JR
        exact xf_rows_mem _ _ (fun x0 x1 => jRowF W Jcols (x2Fl b x0 x1 a)) (fun z => z < 2 ^ (W * x2KeySize 0 b))
          (fun u v => by (try beta_reduce); rw [← hJc]; exact jRowF_lt W Jcols _ hW))
      (by
        intro s hs c hc
        unfold x2F1JR
        rw [xf_rows_getD _ _ (fun x0 x1 => jRowF W Jcols (x2Fl b x0 x1 a)) s hs]
        exact jRowF_ent W Jcols _ c hW (by rw [hJc]; exact hc))
      (fun s _ c _ => ent11_abs_le _ _) hb1 hb2 c c' hc hc']
  rw [xf_sum_range_mul _ (x2KeyMult 0 b 1) (x2KeyMult 0 b 0)]
  apply Finset.sum_congr rfl
  intro x0 hx0
  apply Finset.sum_congr rfl
  intro x1 hx1
  rw [Finset.mem_range] at hx1
  obtain ⟨hdv, hmd⟩ := x2o_divmod x0 x1 (x2KeyMult 0 b 1) hx1
  simp only [hdv, hmd]

/-! ### Part 2, chunk `x₁ = a`: rows `(x₀, a, x₂)`, slot `x₀ m₂ + x₂` -/

/-- A triangle of part 2 at `y₁`: table row `A(t₁, a, y₁)`, type-`t₀` labels, type-`t₂` slots. -/
def x2F2RA (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a y1 : ℕ) : List (List ℕ) :=
  triAOf W (x2KeyMult 0 b 2 * x2KeyMult 0 b 2) (x2UOff0 (x2KeyTypes 0 b 2)) (x2KeyTypes 0 b 0) TA
    (x2AIdx 0 (x2KeyTypes 0 b 1) a y1)

def x2F2G (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a y1 y0 : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).map fun x0 =>
    runComb W (x2KeyMult 0 b 2 * x2KeyMult 0 b 2) (offset W (W - 1) (x2KeyMult 0 b 2 * x2KeyMult 0 b 2))
      (triA (x2F2RA W b TA a y1) x0 y0) (sgnZ x0 y0 * sgnZ a y1)

def x2F2Col (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a y0 y1 y2 : ℕ) : ℕ :=
  concatFibers W (x2KeyMult 0 b 2)
    ((x2F2G W b TA a y1 y0).map (runOf W (x2KeyMult 0 b 2) (y2 * x2KeyMult 0 b 2)))

def x2F2XC (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).flatMap fun y0 => (List.range (x2KeyMult 0 b 1)).flatMap fun y1 =>
    (List.range (x2KeyMult 0 b 2)).map fun y2 => x2F2Col W b TA a y0 y1 y2

def x2F2JR (W : ℕ) (b : x2Key 0) (Jcols : List ℕ) (a : ℕ) : List ℕ :=
  (List.range (x2KeyMult 0 b 0)).flatMap fun x0 => (List.range (x2KeyMult 0 b 2)).map fun x2 =>
    jRowF W Jcols (x2Fl b x0 a x2)

def x2F2Bnd (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a : ℕ) : Bool :=
  (List.range (x2KeyMult 0 b 1)).all fun y1 => (List.range (x2KeyMult 0 b 0)).all fun y0 =>
    (List.range (x2KeyMult 0 b 0)).all fun x0 =>
      (x0 == y0 || a == y1 ||
        slotBoundCheck W bF (x2KeyMult 0 b 2 * x2KeyMult 0 b 2) (triA (x2F2RA W b TA a y1) x0 y0))

noncomputable def x2F2OK (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ)
    (a : ℕ) (lit : List ℕ) : Bool :=
  x2F2Bnd W bF b TA a &&
    decide (x2ChunkO W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 2) Jd (x2F2XC W b TA a)
      (x2F2JR W b Jcols a) = lit)

def x2F2OC (W : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ) (a : ℕ) : List ℕ :=
  x2ChunkOC W (x2KeySize 0 b) (x2KeyMult 0 b 0 * x2KeyMult 0 b 2) Jd (x2F2XC W b TA a) (x2F2JR W b Jcols a)

theorem x2F2XC_ent (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (a : ℕ) (hW : 2 ≤ W) (hbF : bF + 3 ≤ W)
    (ha : a < x2KeyMult 0 b 1) (hbnd : x2F2Bnd W bF b TA a = true)
    (y0 y1 y2 x0 x2 : ℕ) (hy0 : y0 < x2KeyMult 0 b 0) (hy1 : y1 < x2KeyMult 0 b 1) (hy2 : y2 < x2KeyMult 0 b 2)
    (hx0 : x0 < x2KeyMult 0 b 0) (hx2 : x2 < x2KeyMult 0 b 2) :
    ent W (W - 1) ((x2F2XC W b TA a).getD (x2Fl b y0 y1 y2) 0) (x0 * x2KeyMult 0 b 2 + x2) =
        x2X2 W b TA x0 a x2 y0 y1 y2 ∧
      |x2X2 W b TA x0 a x2 y0 y1 y2| ≤ 2 ^ (bF + 1) := by
  have hs : y2 * x2KeyMult 0 b 2 + x2 < x2KeyMult 0 b 2 * x2KeyMult 0 b 2 := x2o_lt_mul y2 x2 _ _ hy2 hx2
  unfold x2F2Bnd at hbnd
  have hc := xf_all3 hbnd y1 y0 x0 hy1 hy0 hx0
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  have hq : x0 < (x2F2G W b TA a y1 y0).length := by simp [x2F2G]; exact hx0
  have hcol : ent W (W - 1) ((x2F2XC W b TA a).getD (x2Fl b y0 y1 y2) 0) (x0 * x2KeyMult 0 b 2 + x2) =
      ent W (W - 1) (runComb W (x2KeyMult 0 b 2 * x2KeyMult 0 b 2)
        (offset W (W - 1) (x2KeyMult 0 b 2 * x2KeyMult 0 b 2)) (triA (x2F2RA W b TA a y1) x0 y0)
        (sgnZ x0 y0 * sgnZ a y1)) (y2 * x2KeyMult 0 b 2 + x2) := by
    unfold x2F2XC x2Fl
    rw [xf_nested_getD _ _ _ (fun y0 y1 y2 => x2F2Col W b TA a y0 y1 y2) y0 y1 y2 hy0 hy1 hy2]
    unfold x2F2Col
    rw [xf_col_ent W (x2KeyMult 0 b 2) (x2F2G W b TA a y1 y0) (y2 * x2KeyMult 0 b 2) x0 x2 hq hx2]
    unfold x2F2G
    rw [x2o_getD_map_range _ x0 _ hx0]
  rw [hcol]
  have h := xf_signed_ent W bF (x2KeyMult 0 b 2) (x2F2RA W b TA a y1) x0 y0 (sgnZ x0 y0 * sgnZ a y1)
    (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 1) a y1) (x2AIdx 0 (x2KeyTypes 0 b 0) x0 y0)) (x2UOff0 (x2KeyTypes 0 b 2))
    (y2 * x2KeyMult 0 b 2 + x2) hW hbF hs (sgnZ_mul_cases _ _ _ _)
    (fun he => triA_eq _ _ _ _ _ _ _ _ hx0 hy0 (x2o_ne_of_sgn _ _ _ _ he).1)
    (fun he => by
      have hne := x2o_ne_of_sgn _ _ _ _ he
      rcases hc with (h | h) | h
      · exact absurd h hne.1
      · exact absurd h hne.2
      · exact h)
  have hX : x2X2 W b TA x0 a x2 y0 y1 y2 = sgnZ x0 y0 * sgnZ a y1 *
      ent W (W - 1) (xfTab TA (x2AIdx 0 (x2KeyTypes 0 b 1) a y1) (x2AIdx 0 (x2KeyTypes 0 b 0) x0 y0))
        (x2UOff0 (x2KeyTypes 0 b 2) + (y2 * x2KeyMult 0 b 2 + x2)) := by
    unfold x2X2
    rw [Nat.add_assoc]
  rw [hX]
  exact h

theorem x2F2OK_sound (W bF : ℕ) (b : x2Key 0) (TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ)
    (a : ℕ) (lit : List ℕ) (hW : 12 ≤ W) (hbF : bF + 3 ≤ W) (ha : a < x2KeyMult 0 b 1)
    (hJc : Jcols.length = x2KeySize 0 b)
    (hJd : ∀ c < x2KeySize 0 b,
      Jd.getD c [] = digs 11 (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (Jcols.getD c 0))
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) < 2 ^ (W - 1))
    (hb2 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 2 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1))
    (hok : x2F2OK W bF b TA Jd Jcols a lit = true) (c c' : ℕ) (hc : c < x2KeySize 0 b)
    (hc' : c' < x2KeySize 0 b) :
    ent W (W - 1) (lit.getD c' 0) c =
      ∑ x0 ∈ Finset.range (x2KeyMult 0 b 0), ∑ x2 ∈ Finset.range (x2KeyMult 0 b 2),
        ent 11 10 (Jcols.getD c 0) (x2Fl b x0 a x2) *
          ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
            x2X2 W b TA x0 a x2 (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i := by
  have hW2 : 2 ≤ W := by omega
  unfold x2F2OK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hbnd, hlit⟩ := hok
  rw [← hlit]
  have hent : ∀ i, i < x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 → ∀ s,
      s < x2KeyMult 0 b 0 * x2KeyMult 0 b 2 →
      ent W (W - 1) ((x2F2XC W b TA a).getD i 0) s =
          x2X2 W b TA (s / x2KeyMult 0 b 2) a (s % x2KeyMult 0 b 2) (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) ∧
        |x2X2 W b TA (s / x2KeyMult 0 b 2) a (s % x2KeyMult 0 b 2) (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i)| ≤
          2 ^ (bF + 1) := by
    intro i hi s hs
    obtain ⟨hd0, hd1, hd2, hfl⟩ := x2Dec_lt b i hi
    obtain ⟨hq, hr, hqr⟩ := xf_mod_div s (x2KeyMult 0 b 2) (x2KeyMult 0 b 0) hs
    have h := x2F2XC_ent W bF b TA a hW2 hbF ha hbnd (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) (s / x2KeyMult 0 b 2)
      (s % x2KeyMult 0 b 2) hd0 hd1 hd2 hq hr
    rw [hfl, hqr] at h
    exact h
  rw [x2ChunkProj W (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (x2KeySize 0 b)
      (x2KeyMult 0 b 0 * x2KeyMult 0 b 2) Jcols Jd (x2F2XC W b TA a) (x2F2JR W b Jcols a)
      (fun s i => x2X2 W b TA (s / x2KeyMult 0 b 2) a (s % x2KeyMult 0 b 2) (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i))
      (fun s c => ent 11 10 (Jcols.getD c 0) (x2Fl b (s / x2KeyMult 0 b 2) a (s % x2KeyMult 0 b 2)))
      (2 ^ (bF + 1)) hW (by positivity) hJd
      (by unfold x2F2XC; exact xf_nested_length _ _ _ _)
      (by
        unfold x2F2XC
        exact xf_nested_mem _ _ _ (fun y0 y1 y2 => x2F2Col W b TA a y0 y1 y2)
          (fun z => z < 2 ^ (W * (x2KeyMult 0 b 0 * x2KeyMult 0 b 2)))
          (fun y0 y1 y2 => xf_col_lt W (x2KeyMult 0 b 2) (x2F2G W b TA a y1 y0) (y2 * x2KeyMult 0 b 2)
            (x2KeyMult 0 b 0) (by simp [x2F2G])))
      (fun i hi s hs => (hent i hi s hs).1) (fun i hi s hs => (hent i hi s hs).2)
      (by unfold x2F2JR; exact xf_rows_length _ _ _)
      (by
        unfold x2F2JR
        exact xf_rows_mem _ _ (fun x0 x2 => jRowF W Jcols (x2Fl b x0 a x2)) (fun z => z < 2 ^ (W * x2KeySize 0 b))
          (fun u v => by (try beta_reduce); rw [← hJc]; exact jRowF_lt W Jcols _ hW))
      (by
        intro s hs c hc
        unfold x2F2JR
        rw [xf_rows_getD _ _ (fun x0 x2 => jRowF W Jcols (x2Fl b x0 a x2)) s hs]
        exact jRowF_ent W Jcols _ c hW (by rw [hJc]; exact hc))
      (fun s _ c _ => ent11_abs_le _ _) hb1 hb2 c c' hc hc']
  rw [xf_sum_range_mul _ (x2KeyMult 0 b 2) (x2KeyMult 0 b 0)]
  apply Finset.sum_congr rfl
  intro x0 hx0
  apply Finset.sum_congr rfl
  intro x2 hx2
  rw [Finset.mem_range] at hx2
  obtain ⟨hdv, hmd⟩ := x2o_divmod x0 x2 (x2KeyMult 0 b 2) hx2
  simp only [hdv, hmd]

/-! ### Assembly: `x2Out` from the three parts, each a sum of chunk values -/

/-- `∑_x J[x, c] ∑_y X[x, y] J[y, c']` over the ambient of block `b` for a part `X` (coordinates as naturals). -/
def x2PartT (b : x2Key 0) (Jcols : List ℕ) (X : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℤ) (c c' : ℕ) : ℤ :=
  ∑ x0 ∈ Finset.range (x2KeyMult 0 b 0), ∑ x1 ∈ Finset.range (x2KeyMult 0 b 1),
    ∑ x2 ∈ Finset.range (x2KeyMult 0 b 2),
      ent 11 10 (Jcols.getD c 0) (x2Fl b x0 x1 x2) *
        ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
          X x0 x1 x2 (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i

/-- A sum over the ambient as a sum over the flat index. -/
theorem xf_sum_amb_flat (m0 m1 m2 : ℕ) (H : ℕ → ℕ → ℕ → ℤ) :
    ∑ x : Fin m0 × Fin m1 × Fin m2, H x.1 x.2.1 x.2.2 =
      ∑ i ∈ Finset.range (m0 * m1 * m2), H (i / (m1 * m2)) ((i / m2) % m1) (i % m2) := by
  rw [← Equiv.sum_comp (x2Flat3 m0 m1 m2).symm, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hv := x2Flat3_val m0 m1 m2 ((x2Flat3 m0 m1 m2).symm i)
  rw [Equiv.apply_symm_apply] at hv
  obtain ⟨e0, e1, e2⟩ := x2o_flat_decode (((x2Flat3 m0 m1 m2).symm i).1 : ℕ) (((x2Flat3 m0 m1 m2).symm i).2.1 : ℕ)
    (((x2Flat3 m0 m1 m2).symm i).2.2 : ℕ) m1 m2 (((x2Flat3 m0 m1 m2).symm i).2.1.isLt)
    (((x2Flat3 m0 m1 m2).symm i).2.2.isLt)
  rw [hv, e0, e1, e2]

/-- A sum over the flat index as a triple sum. -/
theorem xf_sum_flat3 (m0 m1 m2 : ℕ) (H : ℕ → ℕ → ℕ → ℤ) :
    ∑ i ∈ Finset.range (m0 * m1 * m2), H (i / (m1 * m2)) ((i / m2) % m1) (i % m2) =
      ∑ x0 ∈ Finset.range m0, ∑ x1 ∈ Finset.range m1, ∑ x2 ∈ Finset.range m2, H x0 x1 x2 := by
  rw [xf_sum_range_mul _ m2 (m0 * m1), xf_sum_range_mul _ m1 m0]
  apply Finset.sum_congr rfl
  intro x0 _
  apply Finset.sum_congr rfl
  intro x1 hx1
  apply Finset.sum_congr rfl
  intro x2 hx2
  rw [Finset.mem_range] at hx1 hx2
  obtain ⟨e0, e1, e2⟩ := x2o_flat_decode x0 x1 x2 m1 m2 hx1 hx2
  rw [e0, e1, e2]

/-- A sum over the ambient as a triple sum. -/
theorem xf_sum_amb3 (m0 m1 m2 : ℕ) (H : ℕ → ℕ → ℕ → ℤ) :
    ∑ x : Fin m0 × Fin m1 × Fin m2, H x.1 x.2.1 x.2.2 =
      ∑ x0 ∈ Finset.range m0, ∑ x1 ∈ Finset.range m1, ∑ x2 ∈ Finset.range m2, H x0 x1 x2 := by
  rw [xf_sum_amb_flat, xf_sum_flat3]

theorem x2RawH_eq_parts (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0) (W : ℕ) (den : ℚ)
    (TS TA : List (List ℕ)) (hI : X2BlockIface D s Nsrc b W den (xfTab TS) (xfTab TA)) (x y : x2Amb 0 b) :
    x2RawH (x2TransferS D s Nsrc) (x2TransferA D s Nsrc) b x y =
      ((x2X0 W b TS TA x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 + x2X1 W b TA x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 +
        x2X2 W b TA x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 : ℤ) : ℚ) / den := by
  rw [x2RawH_apply, hI.s0 x y, x2o_sgn_term _ _ _ _ _ _ den (hI.a0 x y), x2o_sgn_term _ _ _ _ _ _ den (hI.a1 x y),
    x2o_sgn_term _ _ _ _ _ _ den (hI.a2 x y)]
  unfold x2X0 x2X1 x2X2
  push_cast
  ring

/-- The sum of the three parts of a point `x` against the columns. -/
def x2XS (W : ℕ) (b : x2Key 0) (TS TA : List (List ℕ)) (x0 x1 x2 y0 y1 y2 : ℕ) : ℤ :=
  x2X0 W b TS TA x0 x1 x2 y0 y1 y2 + x2X1 W b TA x0 x1 x2 y0 y1 y2 + x2X2 W b TA x0 x1 x2 y0 y1 y2

theorem x2Out_eq_parts (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0) (W : ℕ) (den : ℚ)
    (TS TA : List (List ℕ)) (Jcols : List ℕ) (hJ : X2ImageCols D b Jcols)
    (hI : X2BlockIface D s Nsrc b W den (xfTab TS) (xfTab TA)) (c c' : x2Col 0 b) :
    x2Out D s Nsrc b c c' =
      ((x2PartT b Jcols (x2X0 W b TS TA) c c' + x2PartT b Jcols (x2X1 W b TA) c c' +
        x2PartT b Jcols (x2X2 W b TA) c c' : ℤ) : ℚ) / den := by
  have hJx : ∀ (x : x2Amb 0 b) (k : x2Col 0 b), ((D.image 0 b).map (Int.cast : ℤ → ℚ)) x k =
      ((ent 11 10 (Jcols.getD k 0) (x2Fl b x.1 x.2.1 x.2.2) : ℤ) : ℚ) := by
    intro x k
    rw [Matrix.map_apply, hJ x k]
    rfl
  have hR : ∀ x y : x2Amb 0 b, x2RawH (x2TransferS D s Nsrc) (x2TransferA D s Nsrc) b x y =
      ((x2XS W b TS TA x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 : ℤ) : ℚ) / den :=
    fun x y => x2RawH_eq_parts D s Nsrc b W den TS TA hI x y
  -- the double sum over the ambient
  have key : x2Out D s Nsrc b c c' = ((∑ x : x2Amb 0 b, ∑ y : x2Amb 0 b,
      ent 11 10 (Jcols.getD c 0) (x2Fl b x.1 x.2.1 x.2.2) *
        (x2XS W b TS TA x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 *
          ent 11 10 (Jcols.getD c' 0) (x2Fl b y.1 y.2.1 y.2.2)) : ℤ) : ℚ) / den := by
    unfold x2Out
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hJx, hR, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [Int.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y _
    push_cast
    ring
  rw [key]
  congr 2
  -- the `y` sums over the flat index
  have hy : ∀ x : x2Amb 0 b, ∑ y : x2Amb 0 b, ent 11 10 (Jcols.getD c 0) (x2Fl b x.1 x.2.1 x.2.2) *
      (x2XS W b TS TA x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2 * ent 11 10 (Jcols.getD c' 0) (x2Fl b y.1 y.2.1 y.2.2)) =
      ent 11 10 (Jcols.getD c 0) (x2Fl b x.1 x.2.1 x.2.2) *
        ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
          x2XS W b TS TA x.1 x.2.1 x.2.2 (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i := by
    intro x
    rw [← Finset.mul_sum]
    congr 1
    refine (xf_sum_amb_flat (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)
      (fun y0 y1 y2 => x2XS W b TS TA x.1 x.2.1 x.2.2 y0 y1 y2 * ent 11 10 (Jcols.getD c' 0) (x2Fl b y0 y1 y2))).trans ?_
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hfl := (x2Dec_lt b i hi).2.2.2
    try beta_reduce
    unfold x2Dec0 x2Dec1 x2Dec2 at hfl ⊢
    rw [hfl]
  rw [Finset.sum_congr rfl (fun x _ => hy x)]
  -- the `x` sum as a triple sum
  rw [xf_sum_amb3 (x2KeyMult 0 b 0) (x2KeyMult 0 b 1) (x2KeyMult 0 b 2)
    (fun x0 x1 x2 => ent 11 10 (Jcols.getD c 0) (x2Fl b x0 x1 x2) *
      ∑ i ∈ Finset.range (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2),
        x2XS W b TS TA x0 x1 x2 (x2Dec0 b i) (x2Dec1 b i) (x2Dec2 b i) * ent 11 10 (Jcols.getD c' 0) i)]
  try beta_reduce
  unfold x2PartT
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x0 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x1 _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x2 _
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold x2XS
  ring

/-- Reorderings of a triple sum. -/
theorem xf_reorder1 (n0 n1 n2 : ℕ) (F : ℕ → ℕ → ℕ → ℤ) :
    ∑ x0 ∈ Finset.range n0, ∑ x1 ∈ Finset.range n1, ∑ x2 ∈ Finset.range n2, F x0 x1 x2 =
      ∑ x2 ∈ Finset.range n2, ∑ x0 ∈ Finset.range n0, ∑ x1 ∈ Finset.range n1, F x0 x1 x2 :=
  (Finset.sum_congr rfl (fun x0 _ => Finset.sum_comm)).trans Finset.sum_comm

theorem xf_reorder0 (n0 n1 n2 : ℕ) (F : ℕ → ℕ → ℕ → ℤ) :
    ∑ x0 ∈ Finset.range n0, ∑ x1 ∈ Finset.range n1, ∑ x2 ∈ Finset.range n2, F x0 x1 x2 =
      ∑ x2 ∈ Finset.range n2, ∑ x1 ∈ Finset.range n1, ∑ x0 ∈ Finset.range n0, F x0 x1 x2 :=
  (xf_reorder1 n0 n1 n2 F).trans (Finset.sum_congr rfl (fun x2 _ => Finset.sum_comm))

theorem xf_reorder2 (n0 n1 n2 : ℕ) (F : ℕ → ℕ → ℕ → ℤ) :
    ∑ x0 ∈ Finset.range n0, ∑ x1 ∈ Finset.range n1, ∑ x2 ∈ Finset.range n2, F x0 x1 x2 =
      ∑ x1 ∈ Finset.range n1, ∑ x0 ∈ Finset.range n0, ∑ x2 ∈ Finset.range n2, F x0 x1 x2 :=
  Finset.sum_comm

/-- `x2Out` of block `b` from chunk literals: the generic theorem behind every block module. -/
theorem x2Out_of_chunks (D : X2Data) (s : Fin 3) (Nsrc : X2Blocks s) (b : x2Key 0) (W bF : ℕ) (den : ℚ)
    (TS TA : List (List ℕ)) (Jd : List (List ℕ)) (Jcols : List ℕ) (L0 L1 L2 : List (List ℕ))
    (O : Matrix (x2Col 0 b) (x2Col 0 b) ℤ)
    (hJ : X2ImageCols D b Jcols) (hI : X2BlockIface D s Nsrc b W den (xfTab TS) (xfTab TA))
    (hW : 12 ≤ W) (hbF : bF + 3 ≤ W) (hJc : Jcols.length = x2KeySize 0 b)
    (hJd : ∀ c < x2KeySize 0 b,
      Jd.getD c [] = digs 11 (x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2) (Jcols.getD c 0))
    (hb1 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) < 2 ^ (W - 1))
    (hb20 : ((x2KeyMult 0 b 1 * x2KeyMult 0 b 0 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1))
    (hb21 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1))
    (hb22 : ((x2KeyMult 0 b 0 * x2KeyMult 0 b 2 : ℕ) : ℤ) *
      (((x2KeyMult 0 b 0 * x2KeyMult 0 b 1 * x2KeyMult 0 b 2 : ℕ) : ℤ) * (2 ^ 10 * 2 ^ (bF + 1)) * 2 ^ 10) <
        2 ^ (W - 1))
    (hok0 : ∀ a < x2KeyMult 0 b 2, x2F0OK W bF b TS TA Jd Jcols a (L0.getD a []) = true)
    (hok1 : ∀ a < x2KeyMult 0 b 2, x2F1OK W bF b TA Jd Jcols a (L1.getD a []) = true)
    (hok2 : ∀ a < x2KeyMult 0 b 1, x2F2OK W bF b TA Jd Jcols a (L2.getD a []) = true)
    (hsum : (Matrix.of fun (c c' : x2Col 0 b) =>
      rsum (fun a => ent W (W - 1) ((L0.getD a []).getD c' 0) c) (x2KeyMult 0 b 2) +
        rsum (fun a => ent W (W - 1) ((L1.getD a []).getD c' 0) c) (x2KeyMult 0 b 2) +
        rsum (fun a => ent W (W - 1) ((L2.getD a []).getD c' 0) c) (x2KeyMult 0 b 1)) = O) :
    x2Out D s Nsrc b = Matrix.of fun (c c' : x2Col 0 b) => ((O c c' : ℤ) : ℚ) / den := by
  ext c c'
  rw [x2Out_eq_parts D s Nsrc b W den TS TA Jcols hJ hI c c', Matrix.of_apply, ← hsum, Matrix.of_apply]
  congr 2
  rw [rsum_eq, rsum_eq, rsum_eq]
  have h0 : x2PartT b Jcols (x2X0 W b TS TA) c c' =
      ∑ a ∈ Finset.range (x2KeyMult 0 b 2), ent W (W - 1) ((L0.getD a []).getD c' 0) c := by
    unfold x2PartT
    rw [xf_reorder0]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    rw [x2F0OK_sound W bF b TS TA Jd Jcols a _ hW hbF ha hJc hJd hb1 hb20 (hok0 a ha) c c' c.isLt c'.isLt]
  have h1 : x2PartT b Jcols (x2X1 W b TA) c c' =
      ∑ a ∈ Finset.range (x2KeyMult 0 b 2), ent W (W - 1) ((L1.getD a []).getD c' 0) c := by
    unfold x2PartT
    rw [xf_reorder1]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    rw [x2F1OK_sound W bF b TA Jd Jcols a _ hW hbF ha hJc hJd hb1 hb21 (hok1 a ha) c c' c.isLt c'.isLt]
  have h2 : x2PartT b Jcols (x2X2 W b TA) c c' =
      ∑ a ∈ Finset.range (x2KeyMult 0 b 1), ent W (W - 1) ((L2.getD a []).getD c' 0) c := by
    unfold x2PartT
    rw [xf_reorder2]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    rw [x2F2OK_sound W bF b TA Jd Jcols a _ hW hbF ha hJc hJd hb1 hb22 (hok2 a ha) c c' c.isLt c'.isLt]
  rw [h0, h1, h2]

end X2
end ThreeCopyQutritWerner
