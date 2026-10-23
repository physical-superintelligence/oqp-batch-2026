module

public import ThreeCopyQutritWerner.CertificateX2OutLemmas

@[expose] public section


/-!
# Output stage: generic reading of `x2RawH` from expanded axis-0 tables

Tables: for a source pipeline `P ∈ {S, A}` a table is a
function `fib k j : ℕ` (`k` the axis-2 label, `j` the axis-1 label); its slot
`x2UOff0 t + a * x2Mult 0 t + b` (width `W`, offset `2^(W-1)`) holds `den` times the transferred value at axis-0
label `x2SIdx 0 t a b`.

On an h block with types `(t₀, t₁, t₂)`, `x2RawH` is the sum of three parts, each read from the tables by runs
of slots of one site:
* part 0 (the `S` term plus the first `A` placement): runs over `x₀`, columns in the order `x2Rot0`;
* part 1 (second `A` placement): runs over `x₁`, order `x2Rot1`;
* part 2 (third `A` placement): runs over `x₂`, order `x2Flat3`.
A column of a part is the concatenation of its pieces (one piece per value of the two other sites), with
`d` pairwise merge passes so that the kernel cost of a concatenation is `O(n log n)`.

The projection `Jᵀ X J` of each part uses the `x2BlockProj`, with `Y = X J` and `Jᵀ Y`
computed by `natAxpyRes` (the checks are then true by construction; the bounds come from the table bounds).
Nothing here depends on certificate data.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Small arithmetic -/

theorem x2o_divmod (a b n : ℕ) (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le b) hb
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem x2o_lt_mul (a b n m : ℕ) (ha : a < m) (hb : b < n) : a * n + b < m * n := by
  calc a * n + b < a * n + n := by omega
    _ = (a + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right _ ha

theorem x2o_flat_decode (y0 y1 y2 m1 m2 : ℕ) (h1 : y1 < m1) (h2 : y2 < m2) :
    ((y0 * m1 + y1) * m2 + y2) / (m1 * m2) = y0 ∧
      (((y0 * m1 + y1) * m2 + y2) / m2) % m1 = y1 ∧ ((y0 * m1 + y1) * m2 + y2) % m2 = y2 := by
  have hq : y1 * m2 + y2 < m1 * m2 := x2o_lt_mul y1 y2 m2 m1 h1 h2
  have e : (y0 * m1 + y1) * m2 + y2 = y0 * (m1 * m2) + (y1 * m2 + y2) := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (x2o_divmod _ _ _ hq).1
  · rw [(x2o_divmod _ _ _ h2).1]
    exact (x2o_divmod _ _ _ h1).2
  · exact (x2o_divmod _ _ _ h2).2

theorem x2o_pow_lt (W : ℕ) (hW : 1 ≤ W) : 2 ^ (W - 1) < 2 ^ W := by
  have hpos : 0 < 2 ^ (W - 1) := by positivity
  have h2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

/-! ### Orientation signs -/

/-- `x2Sgn` over the integers. -/
def sgnZ (a b : ℕ) : ℤ := if a < b then 1 else if b < a then -1 else 0

theorem sgnZ_cases (a b : ℕ) : sgnZ a b = 0 ∨ sgnZ a b = 1 ∨ sgnZ a b = -1 := by
  unfold sgnZ
  split_ifs <;> simp

theorem sgnZ_mul_cases (a b c d : ℕ) :
    sgnZ a b * sgnZ c d = 0 ∨ sgnZ a b * sgnZ c d = 1 ∨ sgnZ a b * sgnZ c d = -1 := by
  rcases sgnZ_cases a b with h | h | h <;> rcases sgnZ_cases c d with h' | h' | h' <;> simp [h, h']

theorem sgnZ_self (a : ℕ) : sgnZ a a = 0 := by simp [sgnZ]

theorem sgnZ_cast (a b : ℕ) : ((sgnZ a b : ℤ) : ℚ) = x2Sgn a b := by
  unfold sgnZ x2Sgn
  split_ifs <;> simp

theorem abs_sgnZ_mul_le (a b c d : ℕ) : |sgnZ a b * sgnZ c d| ≤ 1 := by
  rcases sgnZ_mul_cases a b c d with h | h | h <;> rw [h] <;> simp

theorem x2o_ne_of_sgn (a b c d : ℕ) (h : sgnZ a b * sgnZ c d ≠ 0) : a ≠ b ∧ c ≠ d := by
  constructor
  · intro hab
    subst hab
    simp [sgnZ_self] at h
  · intro hcd
    subst hcd
    simp [sgnZ_self] at h

/-- A signed `A` term of `x2RawH` from its table value (zero when an orientation sign vanishes). -/
theorem x2o_sgn_term (a b c d : ℕ) (V : ℚ) (E : ℤ) (den : ℚ)
    (h : a ≠ b → c ≠ d → V = (E : ℚ) / den) :
    x2Sgn a b * x2Sgn c d * V = ((sgnZ a b * sgnZ c d * E : ℤ) : ℚ) / den := by
  by_cases hab : a = b
  · subst hab
    simp [x2Sgn, sgnZ]
  · by_cases hcd : c = d
    · subst hcd
      simp [x2Sgn, sgnZ]
    · rw [h hab hcd, ← sgnZ_cast, ← sgnZ_cast]
      push_cast
      ring

/-- Bound of `a + e b` for `|a|, |b| ≤ 2^bF`, `|e| ≤ 1` (`b` only matters when `e ≠ 0`). -/
theorem x2o_bound2 (a b e : ℤ) (bF W : ℕ) (hbF : bF + 3 ≤ W) (ha : |a| ≤ 2 ^ bF) (he : |e| ≤ 1)
    (hb : e ≠ 0 → |b| ≤ 2 ^ bF) : |a + e * b| ≤ 2 ^ (bF + 1) ∧ |a + e * b| < 2 ^ (W - 1) := by
  have hp1 : (2 : ℤ) ^ (bF + 1) = 2 * 2 ^ bF := by rw [pow_succ]; ring
  have hpos : (0 : ℤ) < 2 ^ bF := by positivity
  have hexp : bF + 1 < W - 1 := by omega
  have hlt : (2 : ℤ) ^ (bF + 1) < 2 ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) hexp
  have hle : |a + e * b| ≤ 2 ^ (bF + 1) := by
    by_cases h0 : e = 0
    · subst h0
      simp only [zero_mul, add_zero]
      linarith
    · have hb' := hb h0
      calc |a + e * b| ≤ |a| + |e * b| := abs_add_le _ _
        _ = |a| + |e| * |b| := by rw [abs_mul]
        _ ≤ 2 ^ bF + 1 * 2 ^ bF := by
            have : |e| * |b| ≤ 1 * 2 ^ bF :=
              mul_le_mul he hb' (abs_nonneg _) (by norm_num)
            linarith
        _ = 2 ^ (bF + 1) := by rw [hp1]; ring
  exact ⟨hle, lt_of_le_of_lt hle hlt⟩

/-- Bound of `e b` for `|e| ≤ 1` and `|b| ≤ 2^bF` when `e ≠ 0`. -/
theorem x2o_bound1 (e b : ℤ) (bF : ℕ) (he : |e| ≤ 1) (hb : e ≠ 0 → |b| ≤ 2 ^ bF) :
    |e * b| ≤ 2 ^ (bF + 1) := by
  have hp1 : (2 : ℤ) ^ (bF + 1) = 2 * 2 ^ bF := by rw [pow_succ]; ring
  have hpos : (0 : ℤ) < 2 ^ bF := by positivity
  by_cases h0 : e = 0
  · subst h0
    simp only [zero_mul, abs_zero]
    linarith
  · rw [abs_mul]
    have : |e| * |b| ≤ 1 * 2 ^ bF := mul_le_mul he (hb h0) (abs_nonneg _) (by norm_num)
    linarith

/-! ### Balanced concatenation by pairwise merges -/

/-- One merge pass: fibers of `L` slots, pairwise, into fibers of `2L` slots. -/
def mergePairs (W L : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: rest => (a + (b <<< (W * L))) :: mergePairs W L rest

theorem concatFibers_mergePairs (W L : ℕ) : ∀ fs : List ℕ,
    concatFibers W (2 * L) (mergePairs W L fs) = concatFibers W L fs
  | [] => rfl
  | [a] => by simp [mergePairs, concatFibers]
  | a :: b :: rest => by
    simp only [mergePairs, concatFibers, Nat.shiftLeft_eq]
    rw [concatFibers_mergePairs W L rest, show W * (2 * L) = W * L + W * L by ring, pow_add]
    ring

/-- `d` merge passes, the fiber length doubling each time. -/
def mergeIter (W : ℕ) : ℕ → ℕ → List ℕ → List ℕ
  | _, 0, fs => fs
  | L, d + 1, fs => mergeIter W (2 * L) d (mergePairs W L fs)

theorem concatFibers_mergeIter (W : ℕ) : ∀ (d L : ℕ) (fs : List ℕ),
    concatFibers W (2 ^ d * L) (mergeIter W L d fs) = concatFibers W L fs
  | 0, L, fs => by simp [mergeIter]
  | d + 1, L, fs => by
    simp only [mergeIter]
    rw [show 2 ^ (d + 1) * L = 2 ^ d * (2 * L) by ring, concatFibers_mergeIter W d (2 * L),
      concatFibers_mergePairs]

/-- Concatenation of fibers of `L` slots after `d` merge passes. -/
def concatM (W L d : ℕ) (fs : List ℕ) : ℕ := concatFibers W (2 ^ d * L) (mergeIter W L d fs)

theorem concatM_eq (W L d : ℕ) (fs : List ℕ) : concatM W L d fs = concatFibers W L fs :=
  concatFibers_mergeIter W d L fs

/-! ### The offset datum -/

theorem x2o_offset_sum (W L : ℕ) (hW : 1 ≤ W) :
    offset W (W - 1) L = ∑ k ∈ Finset.range L, 2 ^ (W - 1) * (2 ^ W) ^ k := by
  rw [offset, repunit_eq W L hW, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← pow_mul]

theorem x2o_offset_dig (W L s : ℕ) (hW : 1 ≤ W) (hs : s < L) :
    dig W (offset W (W - 1) L) s = 2 ^ (W - 1) := by
  have hlt := x2o_pow_lt W hW
  unfold dig
  rw [x2o_offset_sum W L hW, pow_mul]
  exact sum_digit (2 ^ W) L (fun _ => 2 ^ (W - 1)) (by positivity) (fun _ => hlt) s hs

theorem x2o_ent_offset (W L s : ℕ) (hW : 1 ≤ W) (hs : s < L) :
    ent W (W - 1) (offset W (W - 1) L) s = 0 := by
  unfold ent
  rw [x2o_offset_dig W L s hW hs]
  push_cast
  ring

theorem x2o_offset_lt (W L : ℕ) (hW : 1 ≤ W) : offset W (W - 1) L < 2 ^ (W * L) := by
  have hlt := x2o_pow_lt W hW
  rw [x2o_offset_sum W L hW, pow_mul]
  exact sum_digits_lt (2 ^ W) (fun _ => 2 ^ (W - 1)) (fun _ => hlt) L

/-! ### Lists built from ranges -/

theorem x2o_getD_map_range (n q : ℕ) (g : ℕ → ℕ) (hq : q < n) :
    ((List.range n).map g).getD q 0 = g q := by
  rw [List.getD_eq_getElem _ _ (by simpa using hq)]
  simp

theorem x2o_mem_map_range (n : ℕ) (g : ℕ → ℕ) (P : ℕ → Prop) (h : ∀ q, q < n → P (g q)) :
    ∀ x ∈ (List.range n).map g, P x := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact h q (List.mem_range.mp hq)

theorem ent_runOf (W m off F s : ℕ) (hs : s < m) :
    ent W (W - 1) (runOf W m off F) s = ent W (W - 1) F (off + s) := by
  unfold ent
  rw [dig_runOf W m off F s hs]

/-! ### Columns assembled from pieces -/

/-- A column of `n` pieces of `m` slots (each piece masked to its `m` slots), with `d` merge passes. -/
def colOfPieces (W m d n : ℕ) (piece : ℕ → ℕ) : ℕ :=
  concatM W m d ((List.range n).map fun q => runOf W m 0 (piece q))

theorem colOfPieces_lt (W m d n : ℕ) (piece : ℕ → ℕ) :
    colOfPieces W m d n piece < 2 ^ (W * (m * n)) := by
  unfold colOfPieces
  rw [concatM_eq]
  have h := concatFibers_lt W m _
    (x2o_mem_map_range n (fun q => runOf W m 0 (piece q)) (fun f => f < 2 ^ (W * m))
      (fun q _ => runOf_lt W m 0 (piece q)))
  rw [List.length_map, List.length_range, mul_assoc] at h
  exact h

theorem colOfPieces_ent (W m d n : ℕ) (piece : ℕ → ℕ) (q s : ℕ) (hq : q < n) (hs : s < m) :
    ent W (W - 1) (colOfPieces W m d n piece) (q * m + s) = ent W (W - 1) (piece q) s := by
  unfold colOfPieces
  rw [concatM_eq, ent_concat_runs W m _
      (x2o_mem_map_range n (fun q => runOf W m 0 (piece q)) (fun f => f < 2 ^ (W * m))
        (fun q _ => runOf_lt W m 0 (piece q))) q s (by simpa using hq) hs,
    x2o_getD_map_range n q _ hq, ent_runOf W m 0 (piece q) s hs, zero_add]

/-- Columns of a part, listed in the flat (row-major) order of `y = (y₀, y₁, y₂)`. -/
def x2Cols (m1 m2 n : ℕ) (col : ℕ → ℕ → ℕ → ℕ) : List ℕ :=
  (List.range n).map fun i => col (i / (m1 * m2)) ((i / m2) % m1) (i % m2)

theorem x2Cols_getD (m0 m1 m2 : ℕ) (col : ℕ → ℕ → ℕ → ℕ) (y0 y1 y2 : ℕ) (h0 : y0 < m0)
    (h1 : y1 < m1) (h2 : y2 < m2) :
    (x2Cols m1 m2 (m0 * m1 * m2) col).getD ((y0 * m1 + y1) * m2 + y2) 0 = col y0 y1 y2 := by
  have hlt : (y0 * m1 + y1) * m2 + y2 < m0 * m1 * m2 :=
    x2o_lt_mul _ y2 m2 (m0 * m1) (x2o_lt_mul y0 y1 m1 m0 h0 h1) h2
  unfold x2Cols
  rw [x2o_getD_map_range _ _ _ hlt]
  obtain ⟨e0, e1, e2⟩ := x2o_flat_decode y0 y1 y2 m1 m2 h1 h2
  rw [e0, e1, e2]

/-! ### Computed linear combinations (the check is then true by construction) -/

/-- The output of a natural linear-combination check, computed. -/
noncomputable def natAxpyRes (W L oA : ℕ) (as' Es : List ℕ) : ℕ :=
  Nat.land (Nat.add (natAxpyFold as' (natFibers W L Es) 0) (natAxpyCorr W L oA Es)) (2 ^ (W * L) - 1)

theorem natAxpyCheck_res (W L oA : ℕ) (as' Es : List ℕ) :
    natAxpyCheck W L oA as' Es (natAxpyRes W L oA as' Es) (natAxpyCorr W L oA Es) = true := by
  have h : ∀ X : ℕ, Nat.land X (2 ^ (W * L) - 1) < 2 ^ (W * L) := by
    intro X
    have e : Nat.land X (2 ^ (W * L) - 1) = X % 2 ^ (W * L) :=
      Nat.and_two_pow_sub_one_eq_mod X (W * L)
    rw [e]
    exact Nat.mod_lt _ (by positivity)
  unfold natAxpyCheck natAxpyRes
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, and_true]
  exact h _

/-- `Y = X J` by columns, computed. -/
noncomputable def x2YCols (W N r : ℕ) (Jcols Xcols : List ℕ) : List ℕ :=
  (List.range r).map fun c => natAxpyRes W N 10 (digs 11 N (Jcols.getD c 0)) Xcols

/-- `Jᵀ Y` by columns, computed. -/
noncomputable def x2ORows (W N r : ℕ) (Jcols Xcols Jrows : List ℕ) : List ℕ :=
  (List.range r).map fun c =>
    natAxpyRes W r (W - 1) (digs W N ((x2YCols W N r Jcols Xcols).getD c 0)) Jrows

/-! ### Rows of an image in a chosen slot order -/

/-- Row of an image at flat position `p`: `r` slots of width `W`, offset `2^(W-1)`. -/
def jRowOf (W r : ℕ) (Jcols : List ℕ) (p : ℕ) : ℕ :=
  concatFibers W 1 ((List.range r).map fun c => dig 11 (Jcols.getD c 0) p + 2 ^ (W - 1) - 2 ^ 10)

/-- Rows of an image in the slot order whose position `i` is the flat position `g i`. -/
def jRows (W r N : ℕ) (Jcols : List ℕ) (g : ℕ → ℕ) : List ℕ :=
  (List.range N).map fun i => jRowOf W r Jcols (g i)

theorem x2o_dig_zero (W x : ℕ) : dig W x 0 = x % 2 ^ W := by
  unfold dig
  rw [mul_zero, pow_zero, Nat.div_one]

theorem jRowOf_elem_lt (W p : ℕ) (Jc : ℕ) (hW : 12 ≤ W) :
    dig 11 Jc p + 2 ^ (W - 1) - 2 ^ 10 < 2 ^ (W * 1) := by
  have hd : dig 11 Jc p < 2 ^ 11 := Nat.mod_lt _ (by positivity)
  have h11 : 2 ^ 11 ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
  have e11 : (2 : ℕ) ^ 11 = 2048 := by norm_num
  rw [mul_one]
  omega

theorem jRowOf_lt (W r : ℕ) (Jcols : List ℕ) (p : ℕ) (hW : 12 ≤ W) :
    jRowOf W r Jcols p < 2 ^ (W * r) := by
  unfold jRowOf
  have h := concatFibers_lt W 1 _
    (x2o_mem_map_range r (fun c => dig 11 (Jcols.getD c 0) p + 2 ^ (W - 1) - 2 ^ 10)
      (fun f => f < 2 ^ (W * 1)) (fun c _ => jRowOf_elem_lt W p _ hW))
  rw [List.length_map, List.length_range, mul_one] at h
  exact h

theorem jRowOf_ent (W r : ℕ) (Jcols : List ℕ) (p c : ℕ) (hW : 12 ≤ W) (hc : c < r) :
    ent W (W - 1) (jRowOf W r Jcols p) c = ent 11 10 (Jcols.getD c 0) p := by
  unfold jRowOf
  have hlt := x2o_mem_map_range r (fun c => dig 11 (Jcols.getD c 0) p + 2 ^ (W - 1) - 2 ^ 10)
    (fun f => f < 2 ^ (W * 1)) (fun c _ => jRowOf_elem_lt W p _ hW)
  have h := ent_concat_runs W 1 _ hlt c 0 (by simpa using hc) (by norm_num)
  rw [mul_one, add_zero] at h
  rw [h, x2o_getD_map_range r c _ hc]
  have hv := jRowOf_elem_lt W p (Jcols.getD c 0) hW
  rw [mul_one] at hv
  have hdig : dig W (dig 11 (Jcols.getD c 0) p + 2 ^ (W - 1) - 2 ^ 10) 0 =
      dig 11 (Jcols.getD c 0) p + 2 ^ (W - 1) - 2 ^ 10 := by
    rw [x2o_dig_zero, Nat.mod_eq_of_lt hv]
  unfold ent
  rw [hdig]
  have h10 : 2 ^ 10 ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle : 2 ^ 10 ≤ dig 11 (Jcols.getD c 0) p + 2 ^ (W - 1) := le_trans h10 (Nat.le_add_left _ _)
  rw [Nat.cast_sub hle]
  push_cast
  ring

theorem ent11_abs_le (Jc p : ℕ) : |ent 11 10 Jc p| ≤ 2 ^ 10 := by
  have h0 : (0 : ℤ) ≤ (dig 11 Jc p : ℤ) := by positivity
  have h1 : (dig 11 Jc p : ℤ) < 2 ^ 11 := by exact_mod_cast Nat.mod_lt _ (by positivity)
  unfold ent
  rw [abs_le]
  constructor <;> linarith

/-! ### Projection of one part -/

/-- `Jᵀ X J` of one part, with `Y` and `Jᵀ Y` computed: only bounds are needed. -/
theorem x2PartProj {α : Type*} [Fintype α] (W N r : ℕ) (e f : α ≃ Fin N)
    (Jcols Xcols Jrows : List ℕ) (σ : ℚ) (Xb : ℤ) (hW : 12 ≤ W)
    (hJc : Jcols.length = r) (hX : Xcols.length = N) (hJr : Jrows.length = N)
    (hXlt : ∀ x ∈ Xcols, x < 2 ^ (W * N)) (hJlt : ∀ x ∈ Jrows, x < 2 ^ (W * r))
    (hXb : ∀ i < N, ∀ k < N, |ent W (W - 1) (Xcols.getD i 0) k| ≤ Xb) (hXb0 : 0 ≤ Xb)
    (hJrow : ∀ (x : α) (c : ℕ), c < r →
      ent W (W - 1) (Jrows.getD (e x) 0) c = ent 11 10 (Jcols.getD c 0) (f x))
    (hJb : ∀ i < N, ∀ c < r, |ent W (W - 1) (Jrows.getD i 0) c| ≤ 2 ^ 10)
    (hb1 : (N : ℤ) * (2 ^ 10 * Xb) < 2 ^ (W - 1))
    (hb2 : (N : ℤ) * ((N : ℤ) * (2 ^ 10 * Xb) * 2 ^ 10) < 2 ^ (W - 1))
    (c c' : Fin r) :
    ((Matrix.of fun (x : α) (c : Fin r) => (ent 11 10 (Jcols.getD c 0) (f x) : ℚ))ᵀ *
        (Matrix.of fun (x y : α) => (ent W (W - 1) (Xcols.getD (f y) 0) (e x) : ℚ) / σ) *
        (Matrix.of fun (x : α) (c : Fin r) => (ent 11 10 (Jcols.getD c 0) (f x) : ℚ))) c c' =
      (ent W (W - 1) ((x2ORows W N r Jcols Xcols Jrows).getD c' 0) c : ℚ) / σ := by
  have hYlen : (x2YCols W N r Jcols Xcols).length = r := by simp [x2YCols]
  have hYget : ∀ c < r, (x2YCols W N r Jcols Xcols).getD c 0 =
      natAxpyRes W N 10 (digs 11 N (Jcols.getD c 0)) Xcols := by
    intro c hc
    exact x2o_getD_map_range r c _ hc
  have hYc : ∀ c < r, natAxpyCheck W N 10 (digs 11 N (Jcols.getD c 0)) Xcols
      ((x2YCols W N r Jcols Xcols).getD c 0) (natAxpyCorr W N 10 Xcols) = true := by
    intro c hc
    rw [hYget c hc]
    exact natAxpyCheck_res W N 10 _ _
  have hOc : ∀ c < r, slotCheck W N r Jrows ((x2YCols W N r Jcols Xcols).getD c 0)
      ((x2ORows W N r Jcols Xcols Jrows).getD c 0) = true := by
    intro c hc
    unfold slotCheck
    have hO : (x2ORows W N r Jcols Xcols Jrows).getD c 0 =
        natAxpyRes W r (W - 1) (digs W N ((x2YCols W N r Jcols Xcols).getD c 0)) Jrows :=
      x2o_getD_map_range r c _ hc
    rw [hO]
    exact natAxpyCheck_res W r (W - 1) _ _
  have hYb : ∀ c < r, ∀ k < N,
      |ent W (W - 1) ((x2YCols W N r Jcols Xcols).getD c 0) k| ≤ (N : ℤ) * (2 ^ 10 * Xb) := by
    intro c hc k hk
    have hlinb : ∀ k' < N,
        |lincomb W (sScalars 10 (digs 11 N (Jcols.getD c 0))) Xcols k'| ≤ (N : ℤ) * (2 ^ 10 * Xb) := by
      intro k' hk'
      have hsc : ∀ a ∈ sScalars 10 (digs 11 N (Jcols.getD c 0)), |a| ≤ 2 ^ 10 := by
        intro a ha
        unfold sScalars at ha
        obtain ⟨dd, hd, rfl⟩ := List.mem_map.mp ha
        unfold digs at hd
        obtain ⟨a', _, rfl⟩ := List.mem_map.mp hd
        have hlt : ((Jcols.getD c 0) >>> (11 * a')) &&& (2 ^ 11 - 1) < 2 ^ 11 := by
          rw [Nat.and_two_pow_sub_one_eq_mod]
          exact Nat.mod_lt _ (by positivity)
        have h0 : (0 : ℤ) ≤ ((((Jcols.getD c 0) >>> (11 * a')) &&& (2 ^ 11 - 1) : ℕ) : ℤ) := by
          positivity
        have h1 : ((((Jcols.getD c 0) >>> (11 * a')) &&& (2 ^ 11 - 1) : ℕ) : ℤ) < 2 ^ 11 := by
          exact_mod_cast hlt
        rw [abs_le]
        constructor <;> linarith
      have hfb : ∀ F ∈ Xcols, |ent W (W - 1) F k'| ≤ Xb := by
        intro F hF
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hF
        rw [← List.getD_eq_getElem _ 0 hi]
        exact hXb i (by rw [hX] at hi; exact hi) k' hk'
      have hl := lincomb_abs_le W (2 ^ 10) Xb (by positivity) hXb0 k'
        (sScalars 10 (digs 11 N (Jcols.getD c 0))) Xcols hsc hfb
      simpa [sScalars, digs_length] using hl
    have hs := natAxpyCheck_sound W N 10 (digs 11 N (Jcols.getD c 0)) Xcols _ (by omega)
      (by rw [digs_length, hX]) hXlt (fun k' hk' => lt_of_le_of_lt (hlinb k' hk') hb1) (hYc c hc) k hk
    rw [← hs]
    exact hlinb k hk
  exact x2BlockProj W N r e f Jcols Xcols (x2YCols W N r Jcols Xcols) Jrows
    (x2ORows W N r Jcols Xcols Jrows) σ Xb ((N : ℤ) * (2 ^ 10 * Xb)) hW hJc hX hYlen hJr hXlt hJlt hXb
    hJrow hJb hb1 hYb hb2 (mul_nonneg (Nat.cast_nonneg N) (mul_nonneg (by positivity) hXb0)) hYc hOc c c'

/-! ### Pieces and columns of the three parts -/

/-- Piece `q = x₁ m₂ + x₂` of column `y` of part 0 (`S` plus the first `A` placement): a run over `x₀`. -/
def x2P0Piece (W : ℕ) (t0 t1 t2 : Fin 8) (fibS fibA : ℕ → ℕ → ℕ) (y0 y1 y2 q : ℕ) : ℕ :=
  runComb W (x2Mult 0 t0)
    (runOf W (x2Mult 0 t0) (x2UOff0 t0 + y0 * x2Mult 0 t0)
      (fibS (x2SIdx 0 t2 (q % x2Mult 0 t2) y2) (x2SIdx 0 t1 (q / x2Mult 0 t2) y1)))
    (runOf W (x2Mult 0 t0) (x2UOff0 t0 + y0 * x2Mult 0 t0)
      (fibA (x2AIdx 0 t2 (q % x2Mult 0 t2) y2) (x2AIdx 0 t1 (q / x2Mult 0 t2) y1)))
    (sgnZ (q / x2Mult 0 t2) y1 * sgnZ (q % x2Mult 0 t2) y2)

/-- Piece `q = x₀ m₂ + x₂` of column `y` of part 1 (second `A` placement): a run over `x₁`. -/
def x2P1Piece (W : ℕ) (t0 t1 t2 : Fin 8) (fibA : ℕ → ℕ → ℕ) (y0 y1 y2 q : ℕ) : ℕ :=
  runComb W (x2Mult 0 t1) (offset W (W - 1) (x2Mult 0 t1))
    (runOf W (x2Mult 0 t1) (x2UOff0 t1 + y1 * x2Mult 0 t1)
      (fibA (x2AIdx 0 t2 (q % x2Mult 0 t2) y2) (x2AIdx 0 t0 (q / x2Mult 0 t2) y0)))
    (sgnZ (q / x2Mult 0 t2) y0 * sgnZ (q % x2Mult 0 t2) y2)

/-- Piece `q = x₀ m₁ + x₁` of column `y` of part 2 (third `A` placement): a run over `x₂`. -/
def x2P2Piece (W : ℕ) (t0 t1 t2 : Fin 8) (fibA : ℕ → ℕ → ℕ) (y0 y1 y2 q : ℕ) : ℕ :=
  runComb W (x2Mult 0 t2) (offset W (W - 1) (x2Mult 0 t2))
    (runOf W (x2Mult 0 t2) (x2UOff0 t2 + y2 * x2Mult 0 t2)
      (fibA (x2AIdx 0 t1 (q % x2Mult 0 t1) y1) (x2AIdx 0 t0 (q / x2Mult 0 t1) y0)))
    (sgnZ (q / x2Mult 0 t1) y0 * sgnZ (q % x2Mult 0 t1) y1)

def x2P0Col (W d : ℕ) (t0 t1 t2 : Fin 8) (fibS fibA : ℕ → ℕ → ℕ) (y0 y1 y2 : ℕ) : ℕ :=
  colOfPieces W (x2Mult 0 t0) d (x2Mult 0 t1 * x2Mult 0 t2) (x2P0Piece W t0 t1 t2 fibS fibA y0 y1 y2)

def x2P1Col (W d : ℕ) (t0 t1 t2 : Fin 8) (fibA : ℕ → ℕ → ℕ) (y0 y1 y2 : ℕ) : ℕ :=
  colOfPieces W (x2Mult 0 t1) d (x2Mult 0 t0 * x2Mult 0 t2) (x2P1Piece W t0 t1 t2 fibA y0 y1 y2)

def x2P2Col (W d : ℕ) (t0 t1 t2 : Fin 8) (fibA : ℕ → ℕ → ℕ) (y0 y1 y2 : ℕ) : ℕ :=
  colOfPieces W (x2Mult 0 t2) d (x2Mult 0 t0 * x2Mult 0 t1) (x2P2Piece W t0 t1 t2 fibA y0 y1 y2)

theorem x2P0Col_ent (W d bF : ℕ) (t0 t1 t2 : Fin 8) (fibS fibA : ℕ → ℕ → ℕ)
    (hW : 2 ≤ W) (hbF : bF + 3 ≤ W) (x0 x1 x2 y0 y1 y2 : ℕ)
    (hx0 : x0 < x2Mult 0 t0) (hx1 : x1 < x2Mult 0 t1) (hx2 : x2 < x2Mult 0 t2)
    (hbS : ∀ s < x2Mult 0 t0, |ent W (W - 1) (fibS (x2SIdx 0 t2 x2 y2) (x2SIdx 0 t1 x1 y1))
      (x2UOff0 t0 + y0 * x2Mult 0 t0 + s)| ≤ 2 ^ bF)
    (hbA : x1 ≠ y1 → x2 ≠ y2 → ∀ s < x2Mult 0 t0, |ent W (W - 1)
      (fibA (x2AIdx 0 t2 x2 y2) (x2AIdx 0 t1 x1 y1)) (x2UOff0 t0 + y0 * x2Mult 0 t0 + s)| ≤ 2 ^ bF) :
    ent W (W - 1) (x2P0Col W d t0 t1 t2 fibS fibA y0 y1 y2) ((x1 * x2Mult 0 t2 + x2) * x2Mult 0 t0 + x0) =
      ent W (W - 1) (fibS (x2SIdx 0 t2 x2 y2) (x2SIdx 0 t1 x1 y1)) (x2UOff0 t0 + y0 * x2Mult 0 t0 + x0) +
      sgnZ x1 y1 * sgnZ x2 y2 *
        ent W (W - 1) (fibA (x2AIdx 0 t2 x2 y2) (x2AIdx 0 t1 x1 y1)) (x2UOff0 t0 + y0 * x2Mult 0 t0 + x0) := by
  have hq : x1 * x2Mult 0 t2 + x2 < x2Mult 0 t1 * x2Mult 0 t2 := x2o_lt_mul x1 x2 _ _ hx1 hx2
  unfold x2P0Col
  rw [colOfPieces_ent W _ d _ _ _ x0 hq hx0]
  unfold x2P0Piece
  obtain ⟨hd, hm⟩ := x2o_divmod x1 x2 (x2Mult 0 t2) hx2
  rw [hd, hm]
  have hb : ∀ s < x2Mult 0 t0,
      |ent W (W - 1) (runOf W (x2Mult 0 t0) (x2UOff0 t0 + y0 * x2Mult 0 t0)
          (fibS (x2SIdx 0 t2 x2 y2) (x2SIdx 0 t1 x1 y1))) s +
        sgnZ x1 y1 * sgnZ x2 y2 * ent W (W - 1) (runOf W (x2Mult 0 t0) (x2UOff0 t0 + y0 * x2Mult 0 t0)
          (fibA (x2AIdx 0 t2 x2 y2) (x2AIdx 0 t1 x1 y1))) s| < 2 ^ (W - 1) := by
    intro s hs
    rw [ent_runOf _ _ _ _ s hs, ent_runOf _ _ _ _ s hs]
    refine (x2o_bound2 _ _ (sgnZ x1 y1 * sgnZ x2 y2) bF W hbF (hbS s hs) (abs_sgnZ_mul_le x1 y1 x2 y2)
      ?_).2
    intro h0
    exact hbA (x2o_ne_of_sgn _ _ _ _ h0).1 (x2o_ne_of_sgn _ _ _ _ h0).2 s hs
  rw [runComb_ent W (x2Mult 0 t0) _ _ _ hW (sgnZ_mul_cases _ _ _ _) (runOf_lt _ _ _ _) (runOf_lt _ _ _ _)
    hb x0 hx0, ent_runOf _ _ _ _ x0 hx0, ent_runOf _ _ _ _ x0 hx0]

theorem x2P1Col_ent (W d bF : ℕ) (t0 t1 t2 : Fin 8) (fibA : ℕ → ℕ → ℕ)
    (hW : 2 ≤ W) (hbF : bF + 3 ≤ W) (x0 x1 x2 y0 y1 y2 : ℕ)
    (hx0 : x0 < x2Mult 0 t0) (hx1 : x1 < x2Mult 0 t1) (hx2 : x2 < x2Mult 0 t2)
    (hbA : x0 ≠ y0 → x2 ≠ y2 → ∀ s < x2Mult 0 t1, |ent W (W - 1)
      (fibA (x2AIdx 0 t2 x2 y2) (x2AIdx 0 t0 x0 y0)) (x2UOff0 t1 + y1 * x2Mult 0 t1 + s)| ≤ 2 ^ bF) :
    ent W (W - 1) (x2P1Col W d t0 t1 t2 fibA y0 y1 y2) ((x0 * x2Mult 0 t2 + x2) * x2Mult 0 t1 + x1) =
      sgnZ x0 y0 * sgnZ x2 y2 *
        ent W (W - 1) (fibA (x2AIdx 0 t2 x2 y2) (x2AIdx 0 t0 x0 y0)) (x2UOff0 t1 + y1 * x2Mult 0 t1 + x1) := by
  have hW1 : 1 ≤ W := by omega
  have hq : x0 * x2Mult 0 t2 + x2 < x2Mult 0 t0 * x2Mult 0 t2 := x2o_lt_mul x0 x2 _ _ hx0 hx2
  unfold x2P1Col
  rw [colOfPieces_ent W _ d _ _ _ x1 hq hx1]
  unfold x2P1Piece
  obtain ⟨hd, hm⟩ := x2o_divmod x0 x2 (x2Mult 0 t2) hx2
  rw [hd, hm]
  have hb : ∀ s < x2Mult 0 t1,
      |ent W (W - 1) (offset W (W - 1) (x2Mult 0 t1)) s +
        sgnZ x0 y0 * sgnZ x2 y2 * ent W (W - 1) (runOf W (x2Mult 0 t1) (x2UOff0 t1 + y1 * x2Mult 0 t1)
          (fibA (x2AIdx 0 t2 x2 y2) (x2AIdx 0 t0 x0 y0))) s| < 2 ^ (W - 1) := by
    intro s hs
    rw [x2o_ent_offset W _ s hW1 hs, ent_runOf _ _ _ _ s hs]
    refine (x2o_bound2 0 _ (sgnZ x0 y0 * sgnZ x2 y2) bF W hbF (by rw [abs_zero]; positivity)
      (abs_sgnZ_mul_le x0 y0 x2 y2) ?_).2
    intro h0
    exact hbA (x2o_ne_of_sgn _ _ _ _ h0).1 (x2o_ne_of_sgn _ _ _ _ h0).2 s hs
  rw [runComb_ent W (x2Mult 0 t1) _ _ _ hW (sgnZ_mul_cases _ _ _ _) (x2o_offset_lt W _ hW1)
    (runOf_lt _ _ _ _) hb x1 hx1, x2o_ent_offset W _ x1 hW1 hx1, ent_runOf _ _ _ _ x1 hx1, zero_add]

theorem x2P2Col_ent (W d bF : ℕ) (t0 t1 t2 : Fin 8) (fibA : ℕ → ℕ → ℕ)
    (hW : 2 ≤ W) (hbF : bF + 3 ≤ W) (x0 x1 x2 y0 y1 y2 : ℕ)
    (hx0 : x0 < x2Mult 0 t0) (hx1 : x1 < x2Mult 0 t1) (hx2 : x2 < x2Mult 0 t2)
    (hbA : x0 ≠ y0 → x1 ≠ y1 → ∀ s < x2Mult 0 t2, |ent W (W - 1)
      (fibA (x2AIdx 0 t1 x1 y1) (x2AIdx 0 t0 x0 y0)) (x2UOff0 t2 + y2 * x2Mult 0 t2 + s)| ≤ 2 ^ bF) :
    ent W (W - 1) (x2P2Col W d t0 t1 t2 fibA y0 y1 y2) ((x0 * x2Mult 0 t1 + x1) * x2Mult 0 t2 + x2) =
      sgnZ x0 y0 * sgnZ x1 y1 *
        ent W (W - 1) (fibA (x2AIdx 0 t1 x1 y1) (x2AIdx 0 t0 x0 y0)) (x2UOff0 t2 + y2 * x2Mult 0 t2 + x2) := by
  have hW1 : 1 ≤ W := by omega
  have hq : x0 * x2Mult 0 t1 + x1 < x2Mult 0 t0 * x2Mult 0 t1 := x2o_lt_mul x0 x1 _ _ hx0 hx1
  unfold x2P2Col
  rw [colOfPieces_ent W _ d _ _ _ x2 hq hx2]
  unfold x2P2Piece
  obtain ⟨hd, hm⟩ := x2o_divmod x0 x1 (x2Mult 0 t1) hx1
  rw [hd, hm]
  have hb : ∀ s < x2Mult 0 t2,
      |ent W (W - 1) (offset W (W - 1) (x2Mult 0 t2)) s +
        sgnZ x0 y0 * sgnZ x1 y1 * ent W (W - 1) (runOf W (x2Mult 0 t2) (x2UOff0 t2 + y2 * x2Mult 0 t2)
          (fibA (x2AIdx 0 t1 x1 y1) (x2AIdx 0 t0 x0 y0))) s| < 2 ^ (W - 1) := by
    intro s hs
    rw [x2o_ent_offset W _ s hW1 hs, ent_runOf _ _ _ _ s hs]
    refine (x2o_bound2 0 _ (sgnZ x0 y0 * sgnZ x1 y1) bF W hbF (by rw [abs_zero]; positivity)
      (abs_sgnZ_mul_le x0 y0 x1 y1) ?_).2
    intro h0
    exact hbA (x2o_ne_of_sgn _ _ _ _ h0).1 (x2o_ne_of_sgn _ _ _ _ h0).2 s hs
  rw [runComb_ent W (x2Mult 0 t2) _ _ _ hW (sgnZ_mul_cases _ _ _ _) (x2o_offset_lt W _ hW1)
    (runOf_lt _ _ _ _) hb x2 hx2, x2o_ent_offset W _ x2 hW1 hx2, ent_runOf _ _ _ _ x2 hx2, zero_add]

end X2
end ThreeCopyQutritWerner
