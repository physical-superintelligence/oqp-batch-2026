module

public import ThreeCopyQutritWerner.CertificateX2PackedGlue
public import ThreeCopyQutritWerner.CertificateX2PackedSound
public import ThreeCopyQutritWerner.CertificateX2Reduced

@[expose] public section


/-!
# Contraction core: generic lemmas

A packed three-index tensor is a table of fibers along axis 0: `F.getD j []` is row `j`,
`(F.getD j []).getD c 0` the fiber at `(j, c)`, and slot `i` of that fiber (width `W`, offset
`2^(W-1)`) holds the entry `(i, j, c)`. All three axis contractions of the bridge's
`x2TransferS`/`x2TransferA` are natural linear-combination checks (`natAxpyCheck`):

* `rowCheck`: contraction of the column index `c` of a row (axis 2), and through the columns
  `colOf` of a table, of the row index (axis 1). One check per output fiber; scalars equal to the
  offset `2^oA` (zero coefficients) are skipped (`spPairs`).
* `slotRow`: contraction of the slot index (axis 0). The slots of a data fiber are the scalars
  (`digs`), the fibers are the packed columns of the matrix.

The `x2Axis*` lemmas state the results in the rational form of `CertificateX2Reduced`.
Nothing here depends on certificate data.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-! ### Lists -/

theorem x2c_ofFn_getD (l : List ℕ) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun a : Fin n => l.getD a 0) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [List.getD_eq_getElem _ _ h2]

theorem x2c_getD_mem {α : Type*} (l : List α) (d : α) (j : ℕ) (h : j < l.length) :
    l.getD j d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem lincomb_getD (W oA n k : ℕ) (as Fs : List ℕ) (has : as.length = n) (hFs : Fs.length = n) :
    lincomb W (sScalars oA as) Fs k =
      ∑ a : Fin n, ((as.getD a 0 : ℤ) - 2 ^ oA) * ent W (W - 1) (Fs.getD a 0) k := by
  have h1 := x2c_ofFn_getD as n has
  have h2 := x2c_ofFn_getD Fs n hFs
  calc lincomb W (sScalars oA as) Fs k
      = lincomb W (sScalars oA (List.ofFn (fun a : Fin n => as.getD a 0)))
          (List.ofFn (fun a : Fin n => Fs.getD a 0)) k := by rw [h1, h2]
    _ = _ := by rw [sScalars_ofFn, lincomb_ofFn]

/-! ### Sparse natural linear combinations -/

/-- Scalar/fiber pairs of a row, without the pairs whose scalar is `z` (a zero coefficient in
offset form). -/
def spPairs (z : ℕ) : List ℕ → List ℕ → List (ℕ × ℕ)
  | a :: as, F :: Fs => bif Nat.beq a z then spPairs z as Fs else (a, F) :: spPairs z as Fs
  | _, _ => []

theorem spPairs_mem (z : ℕ) : ∀ (as Fs : List ℕ) (F : ℕ),
    F ∈ (spPairs z as Fs).map Prod.snd → F ∈ Fs
  | [], Fs, F, h => by cases Fs <;> simp [spPairs] at h
  | _ :: _, [], F, h => by simp [spPairs] at h
  | a :: as, G :: Fs, F, h => by
    cases hb : Nat.beq a z
    · simp only [spPairs, hb, cond_false, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · simp [h]
      · exact List.mem_cons_of_mem _ (spPairs_mem z as Fs F h)
    · simp only [spPairs, hb, cond_true] at h
      exact List.mem_cons_of_mem _ (spPairs_mem z as Fs F h)

theorem spPairs_lincomb (W oA k : ℕ) : ∀ (as Fs : List ℕ),
    lincomb W (sScalars oA ((spPairs (2 ^ oA) as Fs).map Prod.fst))
        ((spPairs (2 ^ oA) as Fs).map Prod.snd) k =
      lincomb W (sScalars oA as) Fs k
  | [], Fs => by cases Fs <;> simp [spPairs, sScalars, lincomb]
  | _ :: _, [] => by simp [spPairs, sScalars, lincomb]
  | a :: as, F :: Fs => by
    have ih := spPairs_lincomb W oA k as Fs
    cases hb : Nat.beq a (2 ^ oA)
    · simp only [spPairs, hb, cond_false, List.map_cons, sScalars, lincomb] at ih ⊢
      rw [ih]
    · have ha : a = 2 ^ oA := Nat.eq_of_beq_eq_true hb
      simp only [spPairs, hb, cond_true, List.map_cons, sScalars, lincomb] at ih ⊢
      rw [ih, ha]
      push_cast
      ring

/-- Sparse natural linear-combination check of one output fiber. -/
noncomputable def natAxpySp (W L oA : ℕ) (as Fs : List ℕ) (out : ℕ) : Bool :=
  natAxpyCheck W L oA ((spPairs (2 ^ oA) as Fs).map Prod.fst)
    ((spPairs (2 ^ oA) as Fs).map Prod.snd) out
    (natAxpyCorr W L oA ((spPairs (2 ^ oA) as Fs).map Prod.snd))

theorem natAxpySp_sound (W L oA : ℕ) (as Fs : List ℕ) (out : ℕ) (hW : 2 ≤ W)
    (hE : ∀ F ∈ Fs, F < 2 ^ (W * L))
    (hlin : ∀ k < L, |lincomb W (sScalars oA as) Fs k| < 2 ^ (W - 1))
    (hc : natAxpySp W L oA as Fs out = true) (k : ℕ) (hk : k < L) :
    lincomb W (sScalars oA as) Fs k = ent W (W - 1) out k := by
  rw [← spPairs_lincomb W oA k as Fs]
  exact natAxpyCheck_sound W L oA _ _ out hW (by simp)
    (fun F hF => hE F (spPairs_mem (2 ^ oA) as Fs F hF))
    (fun k' hk' => by rw [spPairs_lincomb W oA k' as Fs]; exact hlin k' hk') hc k hk

/-! ### Row checks: contraction of a column index -/

/-- All outputs of one row: output `o` combines the row's fibers with scalar row `o`. -/
noncomputable def rowCheck (W L oA : ℕ) (Rtab : List (List ℕ)) (Frow Grow : List ℕ) : Bool :=
  (List.zip Rtab Grow).all (fun p => natAxpySp W L oA p.1 Frow p.2)

theorem rowCheck_get (W L oA : ℕ) (Rtab : List (List ℕ)) (Frow Grow : List ℕ) (m : ℕ)
    (hR : Rtab.length = m) (hG : Grow.length = m) (hc : rowCheck W L oA Rtab Frow Grow = true)
    (o : ℕ) (ho : o < m) : natAxpySp W L oA (Rtab.getD o []) Frow (Grow.getD o 0) = true := by
  unfold rowCheck at hc
  have hz : o < (List.zip Rtab Grow).length := by simp [hR, hG, ho]
  have hmem : (Rtab.getD o [], Grow.getD o 0) ∈ List.zip Rtab Grow := by
    have h1 := List.getElem_mem hz
    rw [List.getElem_zip] at h1
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact (List.all_eq_true.mp hc) _ hmem

/-- One row (integer form): `∑_c (Rₒ,c) Fᶜ = Gₒ` slot by slot. -/
theorem rowCheck_int (W L oA n m : ℕ) (Rtab : List (List ℕ)) (Frow Grow : List ℕ) (A B : ℤ)
    (hW : 2 ≤ W) (hR : Rtab.length = m) (hRrow : ∀ o < m, (Rtab.getD o []).length = n)
    (hF : Frow.length = n) (hG : Grow.length = m) (hFr : ∀ x ∈ Frow, x < 2 ^ (W * L))
    (hA : ∀ o < m, ∀ c < n, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hB : ∀ c < n, ∀ k < L, |ent W (W - 1) (Frow.getD c 0) k| ≤ B)
    (hAB : (n : ℤ) * (A * B) < 2 ^ (W - 1)) (h0 : 0 ≤ A)
    (hc : rowCheck W L oA Rtab Frow Grow = true) (o : ℕ) (ho : o < m) (k : ℕ) (hk : k < L) :
    ∑ c : Fin n, (((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA) * ent W (W - 1) (Frow.getD c 0) k =
      ent W (W - 1) (Grow.getD o 0) k := by
  have hs := natAxpySp_sound W L oA (Rtab.getD o []) Frow (Grow.getD o 0) hW hFr ?_
    (rowCheck_get W L oA Rtab Frow Grow m hR hG hc o ho) k hk
  · rwa [lincomb_getD W oA n k _ _ (hRrow o ho) hF] at hs
  · intro k' hk'
    rw [lincomb_getD W oA n k' _ _ (hRrow o ho) hF]
    calc |∑ c : Fin n, (((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA) * ent W (W - 1) (Frow.getD c 0) k'|
        ≤ ∑ c : Fin n, |(((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA) * ent W (W - 1) (Frow.getD c 0) k'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c : Fin n, A * B := by
          apply Finset.sum_le_sum
          intro c _
          rw [abs_mul]
          exact mul_le_mul (hA o ho c c.isLt) (hB c c.isLt k' hk') (abs_nonneg _) h0
      _ = (n : ℤ) * (A * B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < 2 ^ (W - 1) := hAB

theorem rowCheck_bound (W L oA n m : ℕ) (Rtab : List (List ℕ)) (Frow Grow : List ℕ) (A B : ℤ)
    (hW : 2 ≤ W) (hR : Rtab.length = m) (hRrow : ∀ o < m, (Rtab.getD o []).length = n)
    (hF : Frow.length = n) (hG : Grow.length = m) (hFr : ∀ x ∈ Frow, x < 2 ^ (W * L))
    (hA : ∀ o < m, ∀ c < n, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hB : ∀ c < n, ∀ k < L, |ent W (W - 1) (Frow.getD c 0) k| ≤ B)
    (hAB : (n : ℤ) * (A * B) < 2 ^ (W - 1)) (h0 : 0 ≤ A)
    (hc : rowCheck W L oA Rtab Frow Grow = true) (o : ℕ) (ho : o < m) (k : ℕ) (hk : k < L) :
    |ent W (W - 1) (Grow.getD o 0) k| ≤ (n : ℤ) * (A * B) := by
  rw [← rowCheck_int W L oA n m Rtab Frow Grow A B hW hR hRrow hF hG hFr hA hB hAB h0 hc o ho k hk]
  calc |∑ c : Fin n, (((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA) * ent W (W - 1) (Frow.getD c 0) k|
      ≤ ∑ c : Fin n, |(((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA) * ent W (W - 1) (Frow.getD c 0) k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : Fin n, A * B := by
        apply Finset.sum_le_sum
        intro c _
        rw [abs_mul]
        exact mul_le_mul (hA o ho c c.isLt) (hB c c.isLt k hk) (abs_nonneg _) h0
    _ = (n : ℤ) * (A * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Column `k` of a table of rows. -/
def colOf (tab : List (List ℕ)) (k : ℕ) : List ℕ := tab.map (fun row => row.getD k 0)

theorem colOf_length (tab : List (List ℕ)) (k : ℕ) : (colOf tab k).length = tab.length := by
  simp [colOf]

theorem colOf_getD (tab : List (List ℕ)) (k b : ℕ) (hb : b < tab.length) :
    (colOf tab k).getD b 0 = (tab.getD b []).getD k 0 := by
  unfold colOf
  rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map,
    List.getD_eq_getElem _ _ hb]

/-! ### Slot checks: contraction of the slot index -/

/-- The `n` slots (width `W`) of a natural, by shift and mask. -/
def digs (W n x : ℕ) : List ℕ := (List.range n).map (fun a => (x >>> (W * a)) &&& (2 ^ W - 1))

theorem digs_length (W n x : ℕ) : (digs W n x).length = n := by simp [digs]

theorem digs_getD (W n x a : ℕ) (ha : a < n) : (digs W n x).getD a 0 = dig W x a := by
  unfold digs dig
  rw [List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_map, List.getElem_range,
    Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

/-- One output of a slot contraction: the slots of `x` against the packed columns `Cs`. -/
noncomputable def slotCheck (W n m : ℕ) (Cs : List ℕ) (x out : ℕ) : Bool :=
  natAxpyCheck W m (W - 1) (digs W n x) Cs out (natAxpyCorr W m (W - 1) Cs)

theorem slotCheck_int (W n m : ℕ) (Cs : List ℕ) (x out : ℕ) (hW : 2 ≤ W) (hCs : Cs.length = n)
    (hC : ∀ C ∈ Cs, C < 2 ^ (W * m))
    (hlin : ∀ k < m,
      |∑ a : Fin n, ent W (W - 1) x a * ent W (W - 1) (Cs.getD a 0) k| < 2 ^ (W - 1))
    (hc : slotCheck W n m Cs x out = true) (k : ℕ) (hk : k < m) :
    ∑ a : Fin n, ent W (W - 1) x a * ent W (W - 1) (Cs.getD a 0) k = ent W (W - 1) out k := by
  have hsum : ∀ k', lincomb W (sScalars (W - 1) (digs W n x)) Cs k' =
      ∑ a : Fin n, ent W (W - 1) x a * ent W (W - 1) (Cs.getD a 0) k' := by
    intro k'
    rw [lincomb_getD W (W - 1) n k' _ _ (digs_length W n x) hCs]
    apply Finset.sum_congr rfl
    intro a _
    rw [digs_getD W n x a a.isLt]
    rfl
  have h := natAxpyCheck_sound W m (W - 1) (digs W n x) Cs out hW
    (by rw [digs_length, hCs]) hC (fun k' hk' => by rw [hsum]; exact hlin k' hk') hc k hk
  rwa [hsum] at h

/-- All outputs of one row of data fibers. -/
noncomputable def slotRow (W n m : ℕ) (Cs : List ℕ) (Xrow Yrow : List ℕ) : Bool :=
  (List.zip Xrow Yrow).all (fun p => slotCheck W n m Cs p.1 p.2)

theorem slotRow_get (W n m : ℕ) (Cs : List ℕ) (Xrow Yrow : List ℕ) (J : ℕ)
    (hX : Xrow.length = J) (hY : Yrow.length = J) (hc : slotRow W n m Cs Xrow Yrow = true)
    (j : ℕ) (hj : j < J) : slotCheck W n m Cs (Xrow.getD j 0) (Yrow.getD j 0) = true := by
  unfold slotRow at hc
  have hz : j < (List.zip Xrow Yrow).length := by simp [hX, hY, hj]
  have hmem : (Xrow.getD j 0, Yrow.getD j 0) ∈ List.zip Xrow Yrow := by
    have h1 := List.getElem_mem hz
    rw [List.getElem_zip] at h1
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact (List.all_eq_true.mp hc) _ hmem

/-! ### Slot bounds of an offset-`(W-1)` datum -/

/-- Every slot of `E` (offset `2^(W-1)`) has absolute value at most `2^b`. -/
def slotBoundCheck (W b L E : ℕ) : Bool :=
  Nat.blt E (2 ^ (W * L)) && Nat.ble (offset W (W - 1) L) (E + offset W b L) &&
    boundCheck W b L (E + offset W b L - offset W (W - 1) L)

theorem slotBoundCheck_sound (W b L E : ℕ) (hW : b + 2 ≤ W) (h : slotBoundCheck W b L E = true) :
    E < 2 ^ (W * L) ∧ ∀ k < L, |ent W (W - 1) E k| ≤ 2 ^ b := by
  simp only [slotBoundCheck, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨hr, hle⟩, hb⟩ := h
  have hW1 : 1 ≤ W := by omega
  obtain ⟨hr', hb'⟩ := boundCheck_sound W b L _ hW1 (by omega) hb
  refine ⟨hr, fun k hk => ?_⟩
  have e1 := ent_expansion W (W - 1) L E hW1 hr
  have e2 := ent_expansion W b L _ hW1 hr'
  have hcast : (((E + offset W b L - offset W (W - 1) L : ℕ)) : ℤ) =
      (E : ℤ) + (offset W b L : ℤ) - (offset W (W - 1) L : ℤ) := by
    rw [Nat.cast_sub hle, Nat.cast_add]
  rw [hcast] at e2
  have hsum : ∑ k ∈ Finset.range L, ent W (W - 1) E k * 2 ^ (W * k) =
      ∑ k ∈ Finset.range L, ent W b (E + offset W b L - offset W (W - 1) L) k * 2 ^ (W * k) := by
    rw [← e1, ← e2]
    ring
  have hpb : (2 : ℤ) ^ b < 2 ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hc : ∀ k < L, -(2 ^ (W - 1)) ≤ ent W (W - 1) E k ∧ ent W (W - 1) E k < 2 ^ (W - 1) :=
    fun k _ => ent_range W E k hW1
  have hd : ∀ k < L, -(2 ^ (W - 1)) ≤ ent W b (E + offset W b L - offset W (W - 1) L) k ∧
      ent W b (E + offset W b L - offset W (W - 1) L) k < 2 ^ (W - 1) := by
    intro k hk
    have := abs_le.mp (hb' k hk)
    constructor <;> linarith [this.1, this.2]
  rw [balanced_unique W L hW1 _ _ hc hd hsum k hk]
  exact hb' k hk

/-! ### Rational forms of the bridge's axis contractions -/

theorem x2c_sum_div {n : ℕ} (f g : Fin n → ℤ) (den σ : ℚ) (r : ℤ)
    (h : ∑ c, f c * g c = r) :
    ∑ c, ((f c : ℚ) / den) * ((g c : ℚ) / σ) = (r : ℚ) / (den * σ) := by
  rw [← h]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Axis-2 contraction of a table of rows (`x2Axis2`). -/
theorem x2Axis2_rows (W L oA n m J : ℕ) (Rtab F G : List (List ℕ)) (den σ : ℚ) (A B : ℤ)
    (hW : 2 ≤ W) (hR : Rtab.length = m) (hRrow : ∀ o < m, (Rtab.getD o []).length = n)
    (hFrow : ∀ j < J, (F.getD j []).length = n) (hGrow : ∀ j < J, (G.getD j []).length = m)
    (hFr : ∀ j < J, ∀ x ∈ F.getD j [], x < 2 ^ (W * L))
    (hA : ∀ o < m, ∀ c < n, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hB : ∀ j < J, ∀ c < n, ∀ k < L, |ent W (W - 1) ((F.getD j []).getD c 0) k| ≤ B)
    (hAB : (n : ℤ) * (A * B) < 2 ^ (W - 1)) (h0 : 0 ≤ A)
    (hc : ∀ j < J, rowCheck W L oA Rtab (F.getD j []) (G.getD j []) = true)
    (i : Fin L) (j : Fin J) (k : Fin m) :
    x2Axis2 (fun (k : Fin m) (c : Fin n) => ((((Rtab.getD k []).getD c 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den)
        (fun (i : Fin L) (j : Fin J) (c : Fin n) => (ent W (W - 1) ((F.getD j []).getD c 0) i : ℚ) / σ)
        i j k =
      (ent W (W - 1) ((G.getD j []).getD k 0) i : ℚ) / (den * σ) := by
  unfold x2Axis2
  exact x2c_sum_div _ _ den σ _ (rowCheck_int W L oA n m Rtab (F.getD j []) (G.getD j []) A B hW hR
    hRrow (hFrow j j.isLt) (hGrow j j.isLt) (hFr j j.isLt) hA (hB j j.isLt) hAB h0 (hc j j.isLt)
    k k.isLt i i.isLt)

/-- Axis-1 contraction through the columns of a table (`x2Axis1`): output row `k` of `G` lists
the fibers `(j, k)`. -/
theorem x2Axis1_cols (W L oA n m K : ℕ) (Rtab F G : List (List ℕ)) (den σ : ℚ) (A B : ℤ)
    (hW : 2 ≤ W) (hR : Rtab.length = m) (hRrow : ∀ o < m, (Rtab.getD o []).length = n)
    (hF : F.length = n) (hGrow : ∀ k < K, (G.getD k []).length = m)
    (hFr : ∀ b < n, ∀ k < K, (F.getD b []).getD k 0 < 2 ^ (W * L))
    (hA : ∀ o < m, ∀ c < n, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hB : ∀ b < n, ∀ k < K, ∀ i < L, |ent W (W - 1) ((F.getD b []).getD k 0) i| ≤ B)
    (hAB : (n : ℤ) * (A * B) < 2 ^ (W - 1)) (h0 : 0 ≤ A)
    (hc : ∀ k < K, rowCheck W L oA Rtab (colOf F k) (G.getD k []) = true)
    (i : Fin L) (j : Fin m) (k : Fin K) :
    x2Axis1 (fun (j : Fin m) (b : Fin n) => ((((Rtab.getD j []).getD b 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den)
        (fun (i : Fin L) (b : Fin n) (k : Fin K) => (ent W (W - 1) ((F.getD b []).getD k 0) i : ℚ) / σ)
        i j k =
      (ent W (W - 1) ((G.getD k []).getD j 0) i : ℚ) / (den * σ) := by
  unfold x2Axis1
  have hcol : ∀ b : Fin n, (F.getD b []).getD k 0 = (colOf F k).getD b 0 := fun b =>
    (colOf_getD F k b (by rw [hF]; exact b.isLt)).symm
  simp_rw [hcol]
  have hFr' : ∀ x ∈ colOf F k, x < 2 ^ (W * L) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hx
    have hb' : b < n := by rw [colOf_length, hF] at hb; exact hb
    rw [← List.getD_eq_getElem _ 0 hb, colOf_getD F k b (by omega)]
    exact hFr b hb' k k.isLt
  have hB' : ∀ c < n, ∀ i' < L, |ent W (W - 1) ((colOf F k).getD c 0) i'| ≤ B := by
    intro c hc' i' hi'
    rw [colOf_getD F k c (by omega)]
    exact hB c hc' k k.isLt i' hi'
  exact x2c_sum_div _ _ den σ _ (rowCheck_int W L oA n m Rtab (colOf F k) (G.getD k []) A B hW hR
    hRrow (by rw [colOf_length, hF]) (hGrow k k.isLt) hFr' hA hB' hAB h0 (hc k k.isLt)
    j j.isLt i i.isLt)

/-- Axis-0 contraction (`x2Axis0`) of the fibers of a table, by slot checks against the packed
columns `Cs` of the matrix. -/
theorem x2Axis0_slots (W n m J K oA : ℕ) (Rtab F G : List (List ℕ)) (Cs : List ℕ) (den σ : ℚ)
    (A B : ℤ) (hW : 2 ≤ W) (hCs : Cs.length = n) (hC : ∀ C ∈ Cs, C < 2 ^ (W * m))
    (hCe : ∀ a < n, ∀ i < m, ent W (W - 1) (Cs.getD a 0) i = ((Rtab.getD i []).getD a 0 : ℤ) - 2 ^ oA)
    (hFrow : ∀ k < K, (F.getD k []).length = J) (hGrow : ∀ k < K, (G.getD k []).length = J)
    (hA : ∀ o < m, ∀ c < n, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hB : ∀ k < K, ∀ j < J, ∀ a < n, |ent W (W - 1) ((F.getD k []).getD j 0) a| ≤ B)
    (hAB : (n : ℤ) * (B * A) < 2 ^ (W - 1)) (h0 : 0 ≤ B)
    (hc : ∀ k < K, slotRow W n m Cs (F.getD k []) (G.getD k []) = true)
    (i : Fin m) (j : Fin J) (k : Fin K) :
    x2Axis0 (fun (i : Fin m) (a : Fin n) => ((((Rtab.getD i []).getD a 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den)
        (fun (a : Fin n) (j : Fin J) (k : Fin K) => (ent W (W - 1) ((F.getD k []).getD j 0) a : ℚ) / σ)
        i j k =
      (ent W (W - 1) ((G.getD k []).getD j 0) i : ℚ) / (den * σ) := by
  unfold x2Axis0
  have hs := slotCheck_int W n m Cs ((F.getD k []).getD j 0) ((G.getD k []).getD j 0) hW hCs hC
    (by
      intro k' hk'
      calc |∑ a : Fin n, ent W (W - 1) ((F.getD k []).getD j 0) a * ent W (W - 1) (Cs.getD a 0) k'|
          ≤ ∑ a : Fin n, |ent W (W - 1) ((F.getD k []).getD j 0) a * ent W (W - 1) (Cs.getD a 0) k'| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin n, B * A := by
            apply Finset.sum_le_sum
            intro a _
            rw [abs_mul, hCe a a.isLt k' hk']
            exact mul_le_mul (hB k k.isLt j j.isLt a a.isLt) (hA k' hk' a a.isLt) (abs_nonneg _) h0
        _ = (n : ℤ) * (B * A) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < 2 ^ (W - 1) := hAB)
    (slotRow_get W n m Cs (F.getD k []) (G.getD k []) J (hFrow k k.isLt) (hGrow k k.isLt)
      (hc k k.isLt) j j.isLt) i i.isLt
  rw [← hs]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [hCe a a.isLt i i.isLt]
  push_cast
  ring

/-! ### Ranges and shapes -/

theorem natAxpySp_lt (W L oA : ℕ) (as Fs : List ℕ) (out : ℕ)
    (h : natAxpySp W L oA as Fs out = true) : out < 2 ^ (W * L) := by
  unfold natAxpySp natAxpyCheck at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1

theorem rowCheck_lt (W L oA : ℕ) (Rtab : List (List ℕ)) (Frow Grow : List ℕ) (m : ℕ)
    (hR : Rtab.length = m) (hG : Grow.length = m) (hc : rowCheck W L oA Rtab Frow Grow = true)
    (o : ℕ) (ho : o < m) : Grow.getD o 0 < 2 ^ (W * L) :=
  natAxpySp_lt W L oA _ _ _ (rowCheck_get W L oA Rtab Frow Grow m hR hG hc o ho)

theorem slotCheck_lt (W n m : ℕ) (Cs : List ℕ) (x out : ℕ) (h : slotCheck W n m Cs x out = true) :
    out < 2 ^ (W * m) := by
  unfold slotCheck natAxpyCheck at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact h.1

theorem x2c_rows_len (tab : List (List ℕ)) (n : ℕ) (h : tab.all (fun r => r.length == n) = true)
    (j : ℕ) (hj : j < tab.length) : (tab.getD j []).length = n := by
  have := List.all_eq_true.mp h _ (x2c_getD_mem tab [] j hj)
  simpa using this

theorem x2c_all_getD (tab : List (List ℕ)) (P : ℕ → Bool) (h : tab.all (fun r => r.all P) = true)
    (j : ℕ) (hj : j < tab.length) (c : ℕ) (hc : c < (tab.getD j []).length) :
    P ((tab.getD j []).getD c 0) = true := by
  have h1 := List.all_eq_true.mp h _ (x2c_getD_mem tab [] j hj)
  exact List.all_eq_true.mp h1 _ (x2c_getD_mem _ 0 c hc)

theorem x2c_scalar_bound (Rtab : List (List ℕ)) (oA : ℕ)
    (h : Rtab.all (fun r => r.all (fun x => Nat.blt x (2 ^ (oA + 1)))) = true)
    (o : ℕ) (ho : o < Rtab.length) (c : ℕ) (hc : c < (Rtab.getD o []).length) :
    |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ 2 ^ oA := by
  have h1 := x2c_all_getD Rtab _ h o ho c hc
  simp only [Nat.blt_eq] at h1
  have h2 : (((Rtab.getD o []).getD c 0 : ℕ) : ℤ) < 2 ^ (oA + 1) := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ (((Rtab.getD o []).getD c 0 : ℕ) : ℤ) := by positivity
  rw [pow_succ] at h2
  rw [abs_le]
  constructor <;> linarith

/-! ### The three-stage chain -/

/-- `x2Axis0 R0 (x2Axis1 R1 (x2Axis2 R2 T0)) = T3` for packed tables: `T0` has `J` rows of `C`
fibers (`L` slots); `T1` (`J` rows of `m2` fibers) is the axis-2 stage, `T2` (`m2` rows of `m1`
fibers) the axis-1 stage, `T3` (`m2` rows of `m1` fibers of `m0` slots) the axis-0 stage. -/
theorem x2Chain (W L J C m2 m1 m0 oA : ℕ) (R2 R1 R0 T0 T1 T2 T3 : List (List ℕ)) (Cs : List ℕ)
    (den2 den1 den0 σ : ℚ) (A2 A1 A0 B0 : ℤ) (hW : 2 ≤ W)
    (hR2 : R2.length = m2) (hR2r : ∀ o < m2, (R2.getD o []).length = C)
    (hR1 : R1.length = m1) (hR1r : ∀ o < m1, (R1.getD o []).length = J)
    (hA2 : ∀ o < m2, ∀ c < C, |((R2.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A2)
    (hA1 : ∀ o < m1, ∀ c < J, |((R1.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A1)
    (hA0 : ∀ o < m0, ∀ c < L, |((R0.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A0)
    (hT0 : T0.length = J) (hT0r : ∀ j < J, (T0.getD j []).length = C)
    (hT0lt : ∀ j < J, ∀ c < C, (T0.getD j []).getD c 0 < 2 ^ (W * L))
    (hT0b : ∀ j < J, ∀ c < C, ∀ i < L, |ent W (W - 1) ((T0.getD j []).getD c 0) i| ≤ B0)
    (hT1 : T1.length = J) (hT1r : ∀ j < J, (T1.getD j []).length = m2)
    (hc1 : ∀ j < J, rowCheck W L oA R2 (T0.getD j []) (T1.getD j []) = true)
    (hT2r : ∀ k < m2, (T2.getD k []).length = m1)
    (hc2 : ∀ k < m2, rowCheck W L oA R1 (colOf T1 k) (T2.getD k []) = true)
    (hT3r : ∀ k < m2, (T3.getD k []).length = m1)
    (hCs : Cs.length = L) (hC : ∀ x ∈ Cs, x < 2 ^ (W * m0))
    (hCe : ∀ a < L, ∀ i < m0, ent W (W - 1) (Cs.getD a 0) i = ((R0.getD i []).getD a 0 : ℤ) - 2 ^ oA)
    (hc3 : ∀ k < m2, slotRow W L m0 Cs (T2.getD k []) (T3.getD k []) = true)
    (hA2p : 0 ≤ A2) (hA1p : 0 ≤ A1) (hB0p : 0 ≤ B0)
    (hb1 : (C : ℤ) * (A2 * B0) < 2 ^ (W - 1))
    (hb2 : (J : ℤ) * (A1 * ((C : ℤ) * (A2 * B0))) < 2 ^ (W - 1))
    (hb3 : (L : ℤ) * (((J : ℤ) * (A1 * ((C : ℤ) * (A2 * B0)))) * A0) < 2 ^ (W - 1))
    (i : Fin m0) (j : Fin m1) (k : Fin m2) :
    x2Axis0 (fun (i : Fin m0) (a : Fin L) => ((((R0.getD i []).getD a 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den0)
      (x2Axis1 (fun (j : Fin m1) (b : Fin J) => ((((R1.getD j []).getD b 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den1)
        (x2Axis2 (fun (k : Fin m2) (c : Fin C) => ((((R2.getD k []).getD c 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den2)
          (fun (i : Fin L) (j : Fin J) (c : Fin C) =>
            (ent W (W - 1) ((T0.getD j []).getD c 0) i : ℚ) / σ))) i j k =
      (ent W (W - 1) ((T3.getD k []).getD j 0) i : ℚ) / (den0 * (den1 * (den2 * σ))) := by
  -- stage 1
  have hT0mem : ∀ j < J, ∀ x ∈ T0.getD j [], x < 2 ^ (W * L) := by
    intro j hj x hx
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
    rw [← List.getD_eq_getElem _ 0 hc]
    exact hT0lt j hj c (by rw [hT0r j hj] at hc; exact hc)
  have h1 : x2Axis2 (fun (k : Fin m2) (c : Fin C) =>
        ((((R2.getD k []).getD c 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den2)
      (fun (i : Fin L) (j : Fin J) (c : Fin C) => (ent W (W - 1) ((T0.getD j []).getD c 0) i : ℚ) / σ) =
      (fun (i : Fin L) (b : Fin J) (k : Fin m2) =>
        (ent W (W - 1) ((T1.getD b []).getD k 0) i : ℚ) / (den2 * σ)) := by
    funext i' j' k'
    exact x2Axis2_rows W L oA C m2 J R2 T0 T1 den2 σ A2 B0 hW hR2 hR2r hT0r hT1r hT0mem hA2 hT0b
      hb1 hA2p hc1 i' j' k'
  -- bounds of stage 1
  have hT1lt : ∀ b < J, ∀ k < m2, (T1.getD b []).getD k 0 < 2 ^ (W * L) := fun b hb k hk =>
    rowCheck_lt W L oA R2 _ _ m2 hR2 (hT1r b hb) (hc1 b hb) k hk
  have hT1b : ∀ b < J, ∀ k < m2, ∀ i < L,
      |ent W (W - 1) ((T1.getD b []).getD k 0) i| ≤ (C : ℤ) * (A2 * B0) := fun b hb k hk i hi =>
    rowCheck_bound W L oA C m2 R2 _ _ A2 B0 hW hR2 hR2r (hT0r b hb) (hT1r b hb) (hT0mem b hb) hA2
      (hT0b b hb) hb1 hA2p (hc1 b hb) k hk i hi
  -- stage 2
  have h2 : x2Axis1 (fun (j : Fin m1) (b : Fin J) =>
        ((((R1.getD j []).getD b 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den1)
      (fun (i : Fin L) (b : Fin J) (k : Fin m2) =>
        (ent W (W - 1) ((T1.getD b []).getD k 0) i : ℚ) / (den2 * σ)) =
      (fun (a : Fin L) (j : Fin m1) (k : Fin m2) =>
        (ent W (W - 1) ((T2.getD k []).getD j 0) a : ℚ) / (den1 * (den2 * σ))) := by
    funext i' j' k'
    exact x2Axis1_cols W L oA J m1 m2 R1 T1 T2 den1 (den2 * σ) A1 ((C : ℤ) * (A2 * B0)) hW hR1 hR1r
      hT1 hT2r hT1lt hA1 hT1b hb2 hA1p hc2 i' j' k'
  -- bounds of stage 2
  have hT2b : ∀ k < m2, ∀ j < m1, ∀ a < L,
      |ent W (W - 1) ((T2.getD k []).getD j 0) a| ≤ (J : ℤ) * (A1 * ((C : ℤ) * (A2 * B0))) := by
    intro k hk j hj a ha
    have hcolm : ∀ x ∈ colOf T1 k, x < 2 ^ (W * L) := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hx
      have hb' : b < J := by rw [colOf_length, hT1] at hb; exact hb
      rw [← List.getD_eq_getElem _ 0 hb, colOf_getD T1 k b (by omega)]
      exact hT1lt b hb' k hk
    have hcolb : ∀ c < J, ∀ i < L, |ent W (W - 1) ((colOf T1 k).getD c 0) i| ≤
        (C : ℤ) * (A2 * B0) := by
      intro c hc i hi
      rw [colOf_getD T1 k c (by omega)]
      exact hT1b c hc k hk i hi
    exact rowCheck_bound W L oA J m1 R1 (colOf T1 k) (T2.getD k []) A1 ((C : ℤ) * (A2 * B0)) hW
      hR1 hR1r (by rw [colOf_length, hT1]) (hT2r k hk) hcolm hA1 hcolb hb2 hA1p (hc2 k hk) j hj a ha
  have hB1p : 0 ≤ (J : ℤ) * (A1 * ((C : ℤ) * (A2 * B0))) := by positivity
  -- stage 3
  have h3 : x2Axis0 (fun (i : Fin m0) (a : Fin L) =>
        ((((R0.getD i []).getD a 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den0)
      (fun (a : Fin L) (j : Fin m1) (k : Fin m2) =>
        (ent W (W - 1) ((T2.getD k []).getD j 0) a : ℚ) / (den1 * (den2 * σ))) i j k =
      (ent W (W - 1) ((T3.getD k []).getD j 0) i : ℚ) / (den0 * (den1 * (den2 * σ))) :=
    x2Axis0_slots W L m0 m1 m2 oA R0 T2 T3 Cs den0 (den1 * (den2 * σ)) A0
      ((J : ℤ) * (A1 * ((C : ℤ) * (A2 * B0)))) hW hCs hC hCe hT2r hT3r hA0 hT2b hb3 hB1p hc3 i j k
  rw [h1, h2]
  exact h3

/-- First unit index of each sector-0 type in the order `(t, a, b) ↦ off_t + a m_t + b`
(`off_t = ∑_{u<t} m_u²`; type 7 is empty). -/
def x2UOff0 : Fin 8 → ℕ := ![0, 1, 17, 42, 67, 292, 392, 513]

/-! ### Matrix products of literal tables (engine use, e.g. the bridge's per-site identities) -/

/-- `A * B = C` for integer matrices given as data: `A` by rows of offset scalars (`A o c + 2^oA`),
`B` and `C` by packed rows (`p` slots of width `W`, offset `2^(W-1)`); one `rowCheck`. -/
theorem x2MatMul (W p oA n m : ℕ) (A : List (List ℕ)) (Brows Crows : List ℕ) (Ab Bb : ℤ)
    (hW : 2 ≤ W) (hA : A.length = m) (hArow : ∀ o < m, (A.getD o []).length = n)
    (hB : Brows.length = n) (hC : Crows.length = m) (hBr : ∀ x ∈ Brows, x < 2 ^ (W * p))
    (hAb : ∀ o < m, ∀ c < n, |((A.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ Ab)
    (hBb : ∀ c < n, ∀ k < p, |ent W (W - 1) (Brows.getD c 0) k| ≤ Bb)
    (hAB : (n : ℤ) * (Ab * Bb) < 2 ^ (W - 1)) (h0 : 0 ≤ Ab)
    (hc : rowCheck W p oA A Brows Crows = true) :
    (Matrix.of fun (o : Fin m) (c : Fin n) => ((A.getD o []).getD c 0 : ℤ) - 2 ^ oA) *
      (Matrix.of fun (c : Fin n) (k : Fin p) => ent W (W - 1) (Brows.getD c 0) k) =
    Matrix.of fun (o : Fin m) (k : Fin p) => ent W (W - 1) (Crows.getD o 0) k := by
  ext o k
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  exact rowCheck_int W p oA n m A Brows Crows Ab Bb hW hA hArow hB hC hBr hAb hBb hAB h0 hc o o.isLt
    k k.isLt

/-! ### Assembling range checks -/

theorem x2c_range_all (P : ℕ → Bool) (a len : ℕ) (h : (List.range' a len).all P = true) :
    ∀ j, a ≤ j → j < a + len → P j = true := by
  intro j h1 h2
  exact List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem x2c_join (P : ℕ → Prop) (a b c : ℕ) (h1 : ∀ j, a ≤ j → j < b → P j)
    (h2 : ∀ j, b ≤ j → j < c → P j) : ∀ j, a ≤ j → j < c → P j := by
  intro j ha hc
  by_cases hb : j < b
  · exact h1 j ha hb
  · exact h2 j (by omega) hc

end X2
end ThreeCopyQutritWerner
