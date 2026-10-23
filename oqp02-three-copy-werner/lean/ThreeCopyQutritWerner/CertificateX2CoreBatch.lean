module

public import ThreeCopyQutritWerner.CertificateX2OutLemmas

@[expose] public section


/-!
# Contraction core: batched stages

A super-fiber holds `B` consecutive fibers of `n` slots (`B n` slots, width `W`, offset `2^(W-1)`);
fiber number `q` of a batch occupies the slots `q n .. q n + n - 1`. One natural linear-combination
check per super-fiber covers `B` fibers, so the per-output bookkeeping of the kernel (about 40 ms
per output, measured) is shared by `B` fibers.

Layout of the batched chain `x2ChainB` (axis lengths: `n` slots on axis 0, `nb B` on axis 1,
`C` on axis 2):
* `F0` (input): row `J'`, column `c` = super-fiber of the fibers `(j, c)`, `j = J' B + q`;
* `G` (axis-2 stage, `x2Axis2_rowsB`): row `J'`, column `k` (`nk B` columns);
* `H` (regrouped, `regroupFiber`): row `K'`, column `j` = the fibers `(j, k)`, `k = K' B + q`;
* `O` (axis-1 stage, `x2Axis1_rowsB`): row `K'`, column `j'`;
* `T3` (axis-0 stage, `x2Axis0_subB`): row `k`, column `j'` = the output fiber (`m0` slots), from
  the sub-fiber `runOf W n ((k % B) n) (O[k / B][j'])` by a slot check, for the pairs `(j', k)` with
  `P j' k` only.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- Entry of a table of fibers. -/
def x2Tab (T : List (List ℕ)) (k j : ℕ) : ℕ := (T.getD k []).getD j 0

theorem x2b_slot_lt (B n j i : ℕ) (hB : 0 < B) (hi : i < n) : (j % B) * n + i < B * n := by
  have h1 : j % B < B := Nat.mod_lt _ hB
  calc (j % B) * n + i < (j % B) * n + n := by omega
    _ = (j % B + 1) * n := by ring
    _ ≤ B * n := Nat.mul_le_mul_right n h1

theorem x2b_div_lt (B nb j : ℕ) (hj : j < nb * B) : j / B < nb :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)

theorem x2b_mem_lt (T : List (List ℕ)) (r len N : ℕ) (hlen : (T.getD r []).length = len)
    (h : ∀ c < len, x2Tab T r c < N) : ∀ x ∈ T.getD r [], x < N := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
  rw [← List.getD_eq_getElem _ 0 hc]
  exact h c (by rw [hlen] at hc; exact hc)

/-! ### Axis 2, batched over rows -/

theorem x2Axis2_rowsB (W n B nb oA C m : ℕ) (Rtab F G : List (List ℕ)) (den σ : ℚ) (A Bd : ℤ)
    (hW : 2 ≤ W) (hB : 0 < B) (hR : Rtab.length = m) (hRrow : ∀ o < m, (Rtab.getD o []).length = C)
    (hFrow : ∀ J' < nb, (F.getD J' []).length = C) (hGrow : ∀ J' < nb, (G.getD J' []).length = m)
    (hFr : ∀ J' < nb, ∀ x ∈ F.getD J' [], x < 2 ^ (W * (B * n)))
    (hA : ∀ o < m, ∀ c < C, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hBd : ∀ J' < nb, ∀ c < C, ∀ s < B * n, |ent W (W - 1) (x2Tab F J' c) s| ≤ Bd)
    (hAB : (C : ℤ) * (A * Bd) < 2 ^ (W - 1)) (h0 : 0 ≤ A)
    (hc : ∀ J' < nb, rowCheck W (B * n) oA Rtab (F.getD J' []) (G.getD J' []) = true)
    (i : Fin n) (j : Fin (nb * B)) (k : Fin m) :
    x2Axis2 (fun (k : Fin m) (c : Fin C) => ((((Rtab.getD k []).getD c 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den)
        (fun (i : Fin n) (j : Fin (nb * B)) (c : Fin C) =>
          (ent W (W - 1) (x2Tab F (j.val / B) c) ((j.val % B) * n + i.val) : ℚ) / σ) i j k =
      (ent W (W - 1) (x2Tab G (j.val / B) k) ((j.val % B) * n + i.val) : ℚ) / (den * σ) := by
  have hJ := x2b_div_lt B nb j.val j.isLt
  unfold x2Axis2
  exact x2c_sum_div _ _ den σ _ (rowCheck_int W (B * n) oA C m Rtab (F.getD (j.val / B) [])
    (G.getD (j.val / B) []) A Bd hW hR hRrow (hFrow _ hJ) (hGrow _ hJ) (hFr _ hJ) hA
    (hBd _ hJ) hAB h0 (hc _ hJ) k.val k.isLt _ (x2b_slot_lt B n j.val i.val hB i.isLt))

/-! ### Regrouping: from batches over rows to batches over columns -/

/-- Regrouped super-fiber `(kc, b)`: the sub-fibers `(b, kc B + q)`, `q < B`, of the axis-2 stage
table `G` (batched over rows), concatenated. -/
def regroupFiber (W n B : ℕ) (G : List (List ℕ)) (kc b : ℕ) : ℕ :=
  concatFibers W n ((List.range B).map (fun q =>
    runOf W n ((b % B) * n) (x2Tab G (b / B) (kc * B + q))))

theorem regroupFiber_lt (W n B : ℕ) (G : List (List ℕ)) (kc b : ℕ) :
    regroupFiber W n B G kc b < 2 ^ (W * (B * n)) := by
  unfold regroupFiber
  have h := concatFibers_lt W n ((List.range B).map (fun q =>
      runOf W n ((b % B) * n) (x2Tab G (b / B) (kc * B + q))))
    (fun r hr => by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
      exact runOf_lt W n _ _)
  simp only [List.length_map, List.length_range] at h
  have he : W * n * B = W * (B * n) := by ring
  rw [he] at h
  exact h

theorem regroup_ent (W n B : ℕ) (G : List (List ℕ)) (kc b q i : ℕ) (hq : q < B) (hi : i < n) :
    ent W (W - 1) (regroupFiber W n B G kc b) (q * n + i) =
      ent W (W - 1) (x2Tab G (b / B) (kc * B + q)) ((b % B) * n + i) := by
  have hlt : ∀ r ∈ (List.range B).map (fun q' =>
      runOf W n ((b % B) * n) (x2Tab G (b / B) (kc * B + q'))), r < 2 ^ (W * n) := by
    intro r hr
    obtain ⟨q', _, rfl⟩ := List.mem_map.mp hr
    exact runOf_lt W n _ _
  unfold regroupFiber
  rw [ent_concat_runs W n _ hlt q i (by simpa using hq) hi]
  rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map, List.getElem_range]
  unfold ent
  rw [dig_runOf W n _ _ i hi]

/-- Kernel form of one regrouping equation. -/
def regroupOK (W n B : ℕ) (G H : List (List ℕ)) (kc b : ℕ) : Bool :=
  Nat.beq (x2Tab H kc b) (regroupFiber W n B G kc b)

theorem regroupOK_eq (W n B : ℕ) (G H : List (List ℕ)) (kc b : ℕ)
    (h : regroupOK W n B G H kc b = true) : x2Tab H kc b = regroupFiber W n B G kc b :=
  Nat.eq_of_beq_eq_true h

/-- Slots of a regrouped super-fiber: slot `s = q n + i` is slot `(b % B) n + i` of the fiber
`(b / B, kc B + q)` of `G`. -/
theorem regroup_ent_slot (W n B : ℕ) (G : List (List ℕ)) (kc b s : ℕ) (hn : 0 < n) (hs : s < B * n) :
    ent W (W - 1) (regroupFiber W n B G kc b) s =
      ent W (W - 1) (x2Tab G (b / B) (kc * B + s / n)) ((b % B) * n + s % n) := by
  have hq : s / n < B := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hs)
  have h := regroup_ent W n B G kc b (s / n) (s % n) hq (Nat.mod_lt _ hn)
  rw [Nat.div_add_mod' s n] at h
  exact h

/-! ### Axis 1, on the regrouped table -/

theorem x2Axis1_rowsB (W n B nk oA C m : ℕ) (Rtab H O : List (List ℕ)) (den σ : ℚ) (A Bd : ℤ)
    (hW : 2 ≤ W) (hB : 0 < B) (hR : Rtab.length = m) (hRrow : ∀ o < m, (Rtab.getD o []).length = C)
    (hHrow : ∀ K' < nk, (H.getD K' []).length = C) (hOrow : ∀ K' < nk, (O.getD K' []).length = m)
    (hHr : ∀ K' < nk, ∀ x ∈ H.getD K' [], x < 2 ^ (W * (B * n)))
    (hA : ∀ o < m, ∀ c < C, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hBd : ∀ K' < nk, ∀ c < C, ∀ s < B * n, |ent W (W - 1) (x2Tab H K' c) s| ≤ Bd)
    (hAB : (C : ℤ) * (A * Bd) < 2 ^ (W - 1)) (h0 : 0 ≤ A)
    (hc : ∀ K' < nk, rowCheck W (B * n) oA Rtab (H.getD K' []) (O.getD K' []) = true)
    (i : Fin n) (j : Fin m) (k : Fin (nk * B)) :
    x2Axis1 (fun (j : Fin m) (b : Fin C) => ((((Rtab.getD j []).getD b 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den)
        (fun (i : Fin n) (b : Fin C) (k : Fin (nk * B)) =>
          (ent W (W - 1) (x2Tab H (k.val / B) b) ((k.val % B) * n + i.val) : ℚ) / σ) i j k =
      (ent W (W - 1) (x2Tab O (k.val / B) j) ((k.val % B) * n + i.val) : ℚ) / (den * σ) := by
  have hK := x2b_div_lt B nk k.val k.isLt
  unfold x2Axis1
  exact x2c_sum_div _ _ den σ _ (rowCheck_int W (B * n) oA C m Rtab (H.getD (k.val / B) [])
    (O.getD (k.val / B) []) A Bd hW hR hRrow (hHrow _ hK) (hOrow _ hK) (hHr _ hK) hA
    (hBd _ hK) hAB h0 (hc _ hK) j.val j.isLt _ (x2b_slot_lt B n k.val i.val hB i.isLt))

/-! ### Axis 0, on sub-fibers, for the selected pairs -/

theorem x2Axis0_subB (W n B m J K oA : ℕ) (Rtab O T3 : List (List ℕ)) (Cs : List ℕ)
    (P : ℕ → ℕ → Prop) (den σ : ℚ) (A Bd : ℤ) (hW : 2 ≤ W) (hCs : Cs.length = n)
    (hC : ∀ x ∈ Cs, x < 2 ^ (W * m))
    (hCe : ∀ a < n, ∀ i < m, ent W (W - 1) (Cs.getD a 0) i = ((Rtab.getD i []).getD a 0 : ℤ) - 2 ^ oA)
    (hA : ∀ o < m, ∀ c < n, |((Rtab.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A)
    (hBd : ∀ k < K, ∀ j < J, ∀ a < n, |ent W (W - 1) (x2Tab O (k / B) j) ((k % B) * n + a)| ≤ Bd)
    (hAB : (n : ℤ) * (Bd * A) < 2 ^ (W - 1)) (h0 : 0 ≤ Bd)
    (hc : ∀ k < K, ∀ j < J, P j k →
      slotCheck W n m Cs (runOf W n ((k % B) * n) (x2Tab O (k / B) j)) (x2Tab T3 k j) = true)
    (i : Fin m) (j : Fin J) (k : Fin K) (hP : P j.val k.val) :
    x2Axis0 (fun (i : Fin m) (a : Fin n) => ((((Rtab.getD i []).getD a 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den)
        (fun (a : Fin n) (j : Fin J) (k : Fin K) =>
          (ent W (W - 1) (x2Tab O (k.val / B) j) ((k.val % B) * n + a.val) : ℚ) / σ) i j k =
      (ent W (W - 1) (x2Tab T3 k j) i : ℚ) / (den * σ) := by
  have hrun : ∀ a : Fin n, ent W (W - 1) (runOf W n ((k.val % B) * n) (x2Tab O (k.val / B) j.val)) a.val =
      ent W (W - 1) (x2Tab O (k.val / B) j.val) ((k.val % B) * n + a.val) := by
    intro a
    unfold ent
    rw [dig_runOf W n _ _ a.val a.isLt]
  unfold x2Axis0
  have hs := slotCheck_int W n m Cs (runOf W n ((k.val % B) * n) (x2Tab O (k.val / B) j.val))
    (x2Tab T3 k.val j.val) hW hCs hC
    (by
      intro k' hk'
      calc |∑ a : Fin n, ent W (W - 1) (runOf W n ((k.val % B) * n) (x2Tab O (k.val / B) j.val)) a *
              ent W (W - 1) (Cs.getD a 0) k'|
          ≤ ∑ a : Fin n, |ent W (W - 1) (runOf W n ((k.val % B) * n) (x2Tab O (k.val / B) j.val)) a *
              ent W (W - 1) (Cs.getD a 0) k'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin n, Bd * A := by
            apply Finset.sum_le_sum
            intro a _
            rw [abs_mul, hrun a, hCe a a.isLt k' hk']
            exact mul_le_mul (hBd k.val k.isLt j.val j.isLt a.val a.isLt) (hA k' hk' a a.isLt)
              (abs_nonneg _) h0
        _ = (n : ℤ) * (Bd * A) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < 2 ^ (W - 1) := hAB)
    (hc k.val k.isLt j.val j.isLt hP) i.val i.isLt
  rw [← hs]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [hCe a a.isLt i i.isLt, hrun a]
  push_cast
  ring

/-- Pair selection by type lists: `(j, k)` with `type j ≤ type k`. -/
def pOK (tj tk : List ℕ) (j k : ℕ) : Bool := Nat.ble (tj.getD j 0) (tk.getD k 0)

/-! ### The batched three-stage chain -/

/-- `x2Axis0 R0 (x2Axis1 R1 (x2Axis2 R2 T0)) = T3` on the pairs `(j, k)` with `P j k`, for the
batched layout described in the module header. -/
theorem x2ChainB (W n B nb nk C m1 m0 oA : ℕ) (R2 R1 R0 F0 G H O T3 : List (List ℕ))
    (Cs : List ℕ) (P : ℕ → ℕ → Prop) (den2 den1 den0 σ : ℚ) (A2 A1 A0 B0 : ℤ)
    (hW : 2 ≤ W) (hB : 0 < B) (hn : 0 < n)
    (hR2 : R2.length = nk * B) (hR2r : ∀ o < nk * B, (R2.getD o []).length = C)
    (hR1 : R1.length = m1) (hR1r : ∀ o < m1, (R1.getD o []).length = nb * B)
    (hA2 : ∀ o < nk * B, ∀ c < C, |((R2.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A2)
    (hA1 : ∀ o < m1, ∀ c < nb * B, |((R1.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A1)
    (hA0 : ∀ o < m0, ∀ c < n, |((R0.getD o []).getD c 0 : ℤ) - 2 ^ oA| ≤ A0)
    (hF0r : ∀ J' < nb, (F0.getD J' []).length = C)
    (hF0lt : ∀ J' < nb, ∀ c < C, x2Tab F0 J' c < 2 ^ (W * (B * n)))
    (hF0b : ∀ J' < nb, ∀ c < C, ∀ s < B * n, |ent W (W - 1) (x2Tab F0 J' c) s| ≤ B0)
    (hGr : ∀ J' < nb, (G.getD J' []).length = nk * B)
    (hc1 : ∀ J' < nb, rowCheck W (B * n) oA R2 (F0.getD J' []) (G.getD J' []) = true)
    (hHr : ∀ K' < nk, (H.getD K' []).length = nb * B)
    (hreg : ∀ K' < nk, ∀ b < nb * B, x2Tab H K' b = regroupFiber W n B G K' b)
    (hOr : ∀ K' < nk, (O.getD K' []).length = m1)
    (hc2 : ∀ K' < nk, rowCheck W (B * n) oA R1 (H.getD K' []) (O.getD K' []) = true)
    (hCs : Cs.length = n) (hC : ∀ x ∈ Cs, x < 2 ^ (W * m0))
    (hCe : ∀ a < n, ∀ i < m0, ent W (W - 1) (Cs.getD a 0) i = ((R0.getD i []).getD a 0 : ℤ) - 2 ^ oA)
    (hc3 : ∀ k < nk * B, ∀ j < m1, P j k →
      slotCheck W n m0 Cs (runOf W n ((k % B) * n) (x2Tab O (k / B) j)) (x2Tab T3 k j) = true)
    (hA2p : 0 ≤ A2) (hA1p : 0 ≤ A1) (hB0p : 0 ≤ B0)
    (hb1 : (C : ℤ) * (A2 * B0) < 2 ^ (W - 1))
    (hb2 : ((nb * B : ℕ) : ℤ) * (A1 * ((C : ℤ) * (A2 * B0))) < 2 ^ (W - 1))
    (hb3 : (n : ℤ) * ((((nb * B : ℕ) : ℤ) * (A1 * ((C : ℤ) * (A2 * B0)))) * A0) < 2 ^ (W - 1))
    (i : Fin m0) (j : Fin m1) (k : Fin (nk * B)) (hP : P j.val k.val) :
    x2Axis0 (fun (i : Fin m0) (a : Fin n) => ((((R0.getD i []).getD a 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den0)
      (x2Axis1 (fun (j : Fin m1) (b : Fin (nb * B)) =>
          ((((R1.getD j []).getD b 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den1)
        (x2Axis2 (fun (k : Fin (nk * B)) (c : Fin C) =>
            ((((R2.getD k []).getD c 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den2)
          (fun (i : Fin n) (j : Fin (nb * B)) (c : Fin C) =>
            (ent W (W - 1) (x2Tab F0 (j.val / B) c) ((j.val % B) * n + i.val) : ℚ) / σ))) i j k =
      (ent W (W - 1) (x2Tab T3 k j) i : ℚ) / (den0 * (den1 * (den2 * σ))) := by
  -- stage 1 (axis 2), read through the regrouped table
  have hF0mem : ∀ J' < nb, ∀ x ∈ F0.getD J' [], x < 2 ^ (W * (B * n)) := fun J' hJ' =>
    x2b_mem_lt F0 J' C _ (hF0r J' hJ') (hF0lt J' hJ')
  have h1 : x2Axis2 (fun (k : Fin (nk * B)) (c : Fin C) =>
        ((((R2.getD k []).getD c 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den2)
      (fun (i : Fin n) (j : Fin (nb * B)) (c : Fin C) =>
        (ent W (W - 1) (x2Tab F0 (j.val / B) c) ((j.val % B) * n + i.val) : ℚ) / σ) =
      (fun (i : Fin n) (b : Fin (nb * B)) (k : Fin (nk * B)) =>
        (ent W (W - 1) (x2Tab H (k.val / B) b) ((k.val % B) * n + i.val) : ℚ) / (den2 * σ)) := by
    funext i' b' k'
    rw [x2Axis2_rowsB W n B nb oA C (nk * B) R2 F0 G den2 σ A2 B0 hW hB hR2 hR2r hF0r hGr hF0mem
      hA2 hF0b hb1 hA2p hc1 i' b' k',
      hreg (k'.val / B) (x2b_div_lt B nk k'.val k'.isLt) b'.val b'.isLt,
      regroup_ent W n B G (k'.val / B) b'.val (k'.val % B) i'.val (Nat.mod_lt _ hB) i'.isLt,
      Nat.div_add_mod' k'.val B]
  -- bounds of stage 1
  have hGlt : ∀ J' < nb, ∀ k < nk * B, x2Tab G J' k < 2 ^ (W * (B * n)) := fun J' hJ' k hk =>
    rowCheck_lt W (B * n) oA R2 _ _ (nk * B) hR2 (hGr J' hJ') (hc1 J' hJ') k hk
  have hGb : ∀ J' < nb, ∀ k < nk * B, ∀ s < B * n,
      |ent W (W - 1) (x2Tab G J' k) s| ≤ (C : ℤ) * (A2 * B0) := fun J' hJ' k hk s hs =>
    rowCheck_bound W (B * n) oA C (nk * B) R2 _ _ A2 B0 hW hR2 hR2r (hF0r J' hJ') (hGr J' hJ')
      (hF0mem J' hJ') hA2 (hF0b J' hJ') hb1 hA2p (hc1 J' hJ') k hk s hs
  -- regrouping
  have hHlt : ∀ K' < nk, ∀ x ∈ H.getD K' [], x < 2 ^ (W * (B * n)) := fun K' hK' =>
    x2b_mem_lt H K' (nb * B) _ (hHr K' hK') (fun b hb => by
      rw [hreg K' hK' b hb]
      exact regroupFiber_lt W n B G K' b)
  have hHb : ∀ K' < nk, ∀ c < nb * B, ∀ s < B * n,
      |ent W (W - 1) (x2Tab H K' c) s| ≤ (C : ℤ) * (A2 * B0) := by
    intro K' hK' c hc s hs
    rw [hreg K' hK' c hc, regroup_ent_slot W n B G K' c s hn hs]
    have hq : s / n < B := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hs)
    have hk : K' * B + s / n < nk * B := by
      calc K' * B + s / n < K' * B + B := by omega
        _ = (K' + 1) * B := by ring
        _ ≤ nk * B := Nat.mul_le_mul_right B hK'
    exact hGb (c / B) (x2b_div_lt B nb c hc) (K' * B + s / n) hk _
      (x2b_slot_lt B n c (s % n) hB (Nat.mod_lt _ hn))
  -- stage 2 (axis 1)
  have h2 : x2Axis1 (fun (j : Fin m1) (b : Fin (nb * B)) =>
        ((((R1.getD j []).getD b 0 : ℤ) - 2 ^ oA : ℤ) : ℚ) / den1)
      (fun (i : Fin n) (b : Fin (nb * B)) (k : Fin (nk * B)) =>
        (ent W (W - 1) (x2Tab H (k.val / B) b) ((k.val % B) * n + i.val) : ℚ) / (den2 * σ)) =
      (fun (a : Fin n) (j : Fin m1) (k : Fin (nk * B)) =>
        (ent W (W - 1) (x2Tab O (k.val / B) j) ((k.val % B) * n + a.val) : ℚ) / (den1 * (den2 * σ))) := by
    funext i' j' k'
    exact x2Axis1_rowsB W n B nk oA (nb * B) m1 R1 H O den1 (den2 * σ) A1 ((C : ℤ) * (A2 * B0)) hW hB
      hR1 hR1r hHr hOr hHlt hA1 hHb hb2 hA1p hc2 i' j' k'
  -- bounds of stage 2
  have hOb : ∀ k < nk * B, ∀ j < m1, ∀ a < n, |ent W (W - 1) (x2Tab O (k / B) j) ((k % B) * n + a)| ≤
      ((nb * B : ℕ) : ℤ) * (A1 * ((C : ℤ) * (A2 * B0))) := by
    intro k hk j hj a ha
    have hK := x2b_div_lt B nk k hk
    exact rowCheck_bound W (B * n) oA (nb * B) m1 R1 (H.getD (k / B) []) (O.getD (k / B) []) A1
      ((C : ℤ) * (A2 * B0)) hW hR1 hR1r (hHr _ hK) (hOr _ hK) (hHlt _ hK) hA1 (hHb _ hK) hb2 hA1p
      (hc2 _ hK) j hj _ (x2b_slot_lt B n k a hB ha)
  have hB1p : 0 ≤ ((nb * B : ℕ) : ℤ) * (A1 * ((C : ℤ) * (A2 * B0))) := by positivity
  -- stage 3 (axis 0)
  rw [h1, h2]
  exact x2Axis0_subB W n B m0 m1 (nk * B) oA R0 O T3 Cs P den0 (den1 * (den2 * σ)) A0
    (((nb * B : ℕ) : ℤ) * (A1 * ((C : ℤ) * (A2 * B0)))) hW hCs hC hCe hA0 hOb hb3 hB1p hc3 i j k hP

end X2
end ThreeCopyQutritWerner
