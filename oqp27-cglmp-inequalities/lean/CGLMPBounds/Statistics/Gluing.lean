module

public import CGLMPBounds.Scenario.HiddenVariable

@[expose] public section


/-!
# Gluing three contexts of a no-signalling behaviour

Supplement, proof of Theorem F.2: "Delete an edge `e` from the four-cycle. The remaining three
consistent pair distributions extend to a joint distribution on all four outputs by conditional
gluing. [...] Conditionals on zero-marginal events may be chosen arbitrarily. Let `L(e)` be the
resulting local extension. For an optimizer `s` in (B.6), mix these extensions with weights
`1 - s_e`. The local behaviour `L*` satisfies `(L*)_e ≥ s_e q_e`."

For a no-signalling behaviour `q` and a deleted context `(i, j)`, `glue q i j` is the local
hidden-variable model whose hidden variable is the outcome pair `(a', b')` of the opposite context
`(i+1, j+1)`, distributed as `q`. On input `i+1` Alice announces `a'`; on input `i` she samples from
the conditional distribution `q(·, b' | i, j+1) / q_B(b')` (a point mass if `q_B(b') = 0`).
Bob acts symmetrically.

* `isNoSignalling_of_mem_localSet` : Bell-local tables are no-signalling behaviours;
* `glue_mem_localSet`, `glue_apply_of_ne` : the gluing is Bell-local and agrees with `q` on the
  three contexts other than `(i, j)`;
* `exists_local_ge` : for weights `0 ≤ s_e ≤ 1` with `Σ_e s_e = 3` there is a local `L*` with
  `L*_e ≥ s_e q_e` entrywise in every context.
-/

namespace CGLMPBounds

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Local tables are no-signalling behaviours -/

theorem sum_detTable_right (s : Strategy α β) (x y : Fin 2) (a : α) :
    ∑ b, detTable s x y a b = if a = s.1 x then 1 else 0 := by
  unfold detTable
  by_cases h : a = s.1 x <;> simp [h]

theorem sum_detTable_left (s : Strategy α β) (x y : Fin 2) (b : β) :
    ∑ a, detTable s x y a b = if b = s.2 y then 1 else 0 := by
  unfold detTable
  by_cases h : b = s.2 y <;> simp [h]

/-- Every Bell-local table is a no-signalling behaviour. -/
theorem isNoSignalling_of_mem_localSet {L : Table α β} (hL : L ∈ localSet α β) :
    IsNoSignalling L := by
  obtain ⟨w, hw0, hw1, rfl⟩ := mem_localSet_iff.mp hL
  have hmargA : ∀ x y a, ∑ b, (∑ s, w s • detTable s : Table α β) x y a b
      = ∑ s, w s * (if a = s.1 x then 1 else 0) := by
    intro x y a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_detTable_right]
  have hmargB : ∀ x y b, ∑ a, (∑ s, w s • detTable s : Table α β) x y a b
      = ∑ s, w s * (if b = s.2 y then 1 else 0) := by
    intro x y b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_detTable_left]
  refine ⟨⟨fun x y a b => ?_, fun x y => ?_⟩, fun x y y' a => ?_, fun x x' y b => ?_⟩
  · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hw0 s)
      (by unfold detTable; split_ifs <;> norm_num))
  · simp only [hmargA]
    rw [Finset.sum_comm]
    simp [hw1]
  · rw [hmargA, hmargA]
  · rw [hmargB, hmargB]

/-- Elements of the local set are bounded by their normalisation: `t L ≤ q` forces `t ≤ 1`. -/
theorem le_one_of_local_le {q L : Table α β} (hq : IsNoSignalling q) (hL : L ∈ localSet α β)
    {t : ℝ} (htL : ∀ x y a b, t * L x y a b ≤ q x y a b) : t ≤ 1 := by
  have h : ∑ a, ∑ b, t * L 0 0 a b ≤ ∑ a, ∑ b, q 0 0 a b :=
    Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => htL 0 0 a b))
  simp only [← Finset.mul_sum] at h
  rw [(isNoSignalling_of_mem_localSet hL).isBehaviour.sum_eq_one,
    hq.isBehaviour.sum_eq_one, mul_one] at h
  exact h

/-! ### The gluing -/

theorem fin2_eq_or : ∀ x i : Fin 2, x = i ∨ x = i + 1 := by decide

theorem fin2_ne_add_one : ∀ i : Fin 2, i ≠ i + 1 := by decide

/-- Alice's response in the gluing that deletes the context `(i, j)`. -/
def glueA (q : Table α β) (i j : Fin 2) (l : α × β) (x : Fin 2) (a : α) : ℝ :=
  if x = i + 1 then (if a = l.1 then 1 else 0)
  else if ∑ a', q i (j + 1) a' l.2 = 0 then (if a = l.1 then 1 else 0)
  else q i (j + 1) a l.2 / ∑ a', q i (j + 1) a' l.2

/-- Bob's response in the gluing that deletes the context `(i, j)`. -/
def glueB (q : Table α β) (i j : Fin 2) (l : α × β) (y : Fin 2) (b : β) : ℝ :=
  if y = j + 1 then (if b = l.2 then 1 else 0)
  else if ∑ b', q (i + 1) j l.1 b' = 0 then (if b = l.2 then 1 else 0)
  else q (i + 1) j l.1 b / ∑ b', q (i + 1) j l.1 b'

/-- The local extension `L(e)` of the three contexts other than `e = (i, j)`. -/
def glue (q : Table α β) (i j : Fin 2) : Table α β :=
  fun x y a b => ∑ l : α × β, q (i + 1) (j + 1) l.1 l.2 * (glueA q i j l x a * glueB q i j l y b)

theorem glueA_add_one (q : Table α β) (i j : Fin 2) (l : α × β) (a : α) :
    glueA q i j l (i + 1) a = if a = l.1 then 1 else 0 := by
  unfold glueA
  rw [if_pos rfl]

theorem glueA_self (q : Table α β) (i j : Fin 2) (l : α × β) (a : α) :
    glueA q i j l i a = if ∑ a', q i (j + 1) a' l.2 = 0 then (if a = l.1 then 1 else 0)
      else q i (j + 1) a l.2 / ∑ a', q i (j + 1) a' l.2 := by
  unfold glueA
  rw [if_neg (fin2_ne_add_one i)]

theorem glueB_add_one (q : Table α β) (i j : Fin 2) (l : α × β) (b : β) :
    glueB q i j l (j + 1) b = if b = l.2 then 1 else 0 := by
  unfold glueB
  rw [if_pos rfl]

theorem glueB_self (q : Table α β) (i j : Fin 2) (l : α × β) (b : β) :
    glueB q i j l j b = if ∑ b', q (i + 1) j l.1 b' = 0 then (if b = l.2 then 1 else 0)
      else q (i + 1) j l.1 b / ∑ b', q (i + 1) j l.1 b' := by
  unfold glueB
  rw [if_neg (fin2_ne_add_one j)]

theorem glueA_nonneg {q : Table α β} (hq : IsNoSignalling q) (i j : Fin 2) (l : α × β)
    (x : Fin 2) (a : α) : 0 ≤ glueA q i j l x a := by
  unfold glueA
  split_ifs <;> first
    | exact zero_le_one
    | exact le_refl 0
    | exact div_nonneg (hq.isBehaviour.nonneg _ _ _ _)
        (Finset.sum_nonneg (fun a' _ => hq.isBehaviour.nonneg _ _ _ _))

theorem glueB_nonneg {q : Table α β} (hq : IsNoSignalling q) (i j : Fin 2) (l : α × β)
    (y : Fin 2) (b : β) : 0 ≤ glueB q i j l y b := by
  unfold glueB
  split_ifs <;> first
    | exact zero_le_one
    | exact le_refl 0
    | exact div_nonneg (hq.isBehaviour.nonneg _ _ _ _)
        (Finset.sum_nonneg (fun b' _ => hq.isBehaviour.nonneg _ _ _ _))

theorem sum_glueA (q : Table α β) (i j : Fin 2) (l : α × β) (x : Fin 2) :
    ∑ a, glueA q i j l x a = 1 := by
  rcases fin2_eq_or x i with hx | hx <;> rw [hx]
  · by_cases hS : ∑ a', q i (j + 1) a' l.2 = 0
    · have h2 : ∀ a, glueA q i j l i a = if a = l.1 then 1 else 0 := fun a => by
        rw [glueA_self, if_pos hS]
      rw [Finset.sum_congr rfl (fun a _ => h2 a)]
      simp
    · have h2 : ∀ a, glueA q i j l i a = q i (j + 1) a l.2 / ∑ a', q i (j + 1) a' l.2 :=
        fun a => by rw [glueA_self, if_neg hS]
      rw [Finset.sum_congr rfl (fun a _ => h2 a), ← Finset.sum_div, div_self hS]
  · rw [Finset.sum_congr rfl (fun a _ => glueA_add_one q i j l a)]
    simp

theorem sum_glueB (q : Table α β) (i j : Fin 2) (l : α × β) (y : Fin 2) :
    ∑ b, glueB q i j l y b = 1 := by
  rcases fin2_eq_or y j with hy | hy <;> rw [hy]
  · by_cases hS : ∑ b', q (i + 1) j l.1 b' = 0
    · have h2 : ∀ b, glueB q i j l j b = if b = l.2 then 1 else 0 := fun b => by
        rw [glueB_self, if_pos hS]
      rw [Finset.sum_congr rfl (fun b _ => h2 b)]
      simp
    · have h2 : ∀ b, glueB q i j l j b = q (i + 1) j l.1 b / ∑ b', q (i + 1) j l.1 b' :=
        fun b => by rw [glueB_self, if_neg hS]
      rw [Finset.sum_congr rfl (fun b _ => h2 b), ← Finset.sum_div, div_self hS]
  · rw [Finset.sum_congr rfl (fun b _ => glueB_add_one q i j l b)]
    simp

/-- The gluing is a Bell-local table (a finite local hidden-variable model). -/
theorem glue_mem_localSet {q : Table α β} (hq : IsNoSignalling q) (i j : Fin 2) :
    glue q i j ∈ localSet α β := by
  have hp1 : ∑ l : α × β, q (i + 1) (j + 1) l.1 l.2 = 1 := by
    rw [Fintype.sum_prod_type']
    exact hq.isBehaviour.sum_eq_one _ _
  exact lhv_mem_localSet (fun l : α × β => q (i + 1) (j + 1) l.1 l.2)
    (fun l => hq.isBehaviour.nonneg _ _ _ _) hp1 (glueA q i j) (glueB q i j)
    (glueA_nonneg hq i j) (sum_glueA q i j) (glueB_nonneg hq i j) (sum_glueB q i j)

theorem glue_nonneg {q : Table α β} (hq : IsNoSignalling q) (i j x y : Fin 2) (a : α) (b : β) :
    0 ≤ glue q i j x y a b := by
  unfold glue
  exact Finset.sum_nonneg (fun l _ => mul_nonneg (hq.isBehaviour.nonneg _ _ _ _)
    (mul_nonneg (glueA_nonneg hq i j l x a) (glueB_nonneg hq i j l y b)))

theorem sum_pair_snd (G : α × β → ℝ) (b : β) :
    ∑ l : α × β, G l * (if b = l.2 then 1 else 0) = ∑ a', G (a', b) := by
  rw [Fintype.sum_prod_type]
  simp

theorem sum_pair_fst (G : α × β → ℝ) (a : α) :
    ∑ l : α × β, (if a = l.1 then 1 else 0) * G l = ∑ b', G (a, b') := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- On the context opposite to the deleted one, the gluing reproduces `q`. -/
theorem glue_apply_center (q : Table α β) (i j : Fin 2) (a : α) (b : β) :
    glue q i j (i + 1) (j + 1) a b = q (i + 1) (j + 1) a b := by
  show ∑ l : α × β, q (i + 1) (j + 1) l.1 l.2
      * (glueA q i j l (i + 1) a * glueB q i j l (j + 1) b) = _
  simp only [glueA_add_one, glueB_add_one]
  rw [Fintype.sum_eq_single (a, b)]
  · simp
  · intro l hl
    by_cases h1 : a = l.1
    · by_cases h2 : b = l.2
      · exact absurd (Prod.ext h1.symm h2.symm) hl
      · simp [h2]
    · simp [h1]

/-- On the context `(i, j+1)` the gluing reproduces `q`. -/
theorem glue_apply_left {q : Table α β} (hq : IsNoSignalling q) (i j : Fin 2) (a : α) (b : β) :
    glue q i j i (j + 1) a b = q i (j + 1) a b := by
  have hB : ∑ a', q (i + 1) (j + 1) a' b = ∑ a', q i (j + 1) a' b :=
    hq.margB_indep (i + 1) i (j + 1) b
  have h1 : glue q i j i (j + 1) a b
      = ∑ a', q (i + 1) (j + 1) a' b * glueA q i j (a', b) i a := by
    have e : ∀ l : α × β, q (i + 1) (j + 1) l.1 l.2 * (glueA q i j l i a * glueB q i j l (j + 1) b)
        = q (i + 1) (j + 1) l.1 l.2 * glueA q i j l i a * (if b = l.2 then 1 else 0) := by
      intro l
      rw [glueB_add_one, mul_assoc]
    show ∑ l : α × β, q (i + 1) (j + 1) l.1 l.2
        * (glueA q i j l i a * glueB q i j l (j + 1) b) = _
    rw [Finset.sum_congr rfl (fun l _ => e l)]
    exact sum_pair_snd (fun l => q (i + 1) (j + 1) l.1 l.2 * glueA q i j l i a) b
  rw [h1]
  by_cases hS : ∑ a', q i (j + 1) a' b = 0
  · have hz : ∀ a', q (i + 1) (j + 1) a' b = 0 := fun a' =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun a'' _ => hq.isBehaviour.nonneg _ _ _ _)).mp
        (hB.trans hS) a' (Finset.mem_univ _)
    have hzq : q i (j + 1) a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a'' _ => hq.isBehaviour.nonneg _ _ _ _)).mp
        hS a (Finset.mem_univ _)
    rw [hzq]
    exact Finset.sum_eq_zero (fun a' _ => by rw [hz a', zero_mul])
  · have h2 : ∀ a', glueA q i j (a', b) i a = q i (j + 1) a b / ∑ a'', q i (j + 1) a'' b :=
      fun a' => by simp only [glueA_self, if_neg hS]
    simp only [h2]
    rw [← Finset.sum_mul, hB, ← mul_div_assoc, mul_div_cancel_left₀ _ hS]

/-- On the context `(i+1, j)` the gluing reproduces `q`. -/
theorem glue_apply_right {q : Table α β} (hq : IsNoSignalling q) (i j : Fin 2) (a : α) (b : β) :
    glue q i j (i + 1) j a b = q (i + 1) j a b := by
  have hA : ∑ b', q (i + 1) (j + 1) a b' = ∑ b', q (i + 1) j a b' :=
    hq.margA_indep (i + 1) (j + 1) j a
  have h1 : glue q i j (i + 1) j a b
      = ∑ b', q (i + 1) (j + 1) a b' * glueB q i j (a, b') j b := by
    have e : ∀ l : α × β, q (i + 1) (j + 1) l.1 l.2 * (glueA q i j l (i + 1) a * glueB q i j l j b)
        = (if a = l.1 then 1 else 0) * (q (i + 1) (j + 1) l.1 l.2 * glueB q i j l j b) := by
      intro l
      rw [glueA_add_one]
      ring
    show ∑ l : α × β, q (i + 1) (j + 1) l.1 l.2
        * (glueA q i j l (i + 1) a * glueB q i j l j b) = _
    rw [Finset.sum_congr rfl (fun l _ => e l)]
    exact sum_pair_fst (fun l => q (i + 1) (j + 1) l.1 l.2 * glueB q i j l j b) a
  rw [h1]
  by_cases hS : ∑ b', q (i + 1) j a b' = 0
  · have hz : ∀ b', q (i + 1) (j + 1) a b' = 0 := fun b' =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun b'' _ => hq.isBehaviour.nonneg _ _ _ _)).mp
        (hA.trans hS) b' (Finset.mem_univ _)
    have hzq : q (i + 1) j a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b'' _ => hq.isBehaviour.nonneg _ _ _ _)).mp
        hS b (Finset.mem_univ _)
    rw [hzq]
    exact Finset.sum_eq_zero (fun b' _ => by rw [hz b', zero_mul])
  · have h2 : ∀ b', glueB q i j (a, b') j b = q (i + 1) j a b / ∑ b'', q (i + 1) j a b'' :=
      fun b' => by simp only [glueB_self, if_neg hS]
    simp only [h2]
    rw [← Finset.sum_mul, hA, ← mul_div_assoc, mul_div_cancel_left₀ _ hS]

/-- The gluing that deletes `(i, j)` agrees with `q` on the three other contexts. -/
theorem glue_apply_of_ne {q : Table α β} (hq : IsNoSignalling q) (i j : Fin 2) {x y : Fin 2}
    (hxy : ¬(x = i ∧ y = j)) (a : α) (b : β) : glue q i j x y a b = q x y a b := by
  rcases fin2_eq_or x i with hx | hx <;> rcases fin2_eq_or y j with hy | hy <;> rw [hx, hy]
  · exact absurd ⟨hx, hy⟩ hxy
  · exact glue_apply_left hq i j a b
  · exact glue_apply_right hq i j a b
  · exact glue_apply_center q i j a b

/-- Proof of Theorem F.2, first step: for weights `0 ≤ s_e ≤ 1` with `Σ_e s_e = 3`, the mixture
`L* = Σ_e (1 - s_e) L(e)` of the four gluings is local and satisfies `L*_e ≥ s_e q_e`. -/
theorem exists_local_ge {q : Table α β} (hq : IsNoSignalling q) {s : Fin 2 → Fin 2 → ℝ}
    (hs : ∀ x y, 0 ≤ s x y ∧ s x y ≤ 1) (hs3 : ∑ x, ∑ y, s x y = 3) :
    ∃ L ∈ localSet α β, ∀ x y a b, s x y * q x y a b ≤ L x y a b := by
  have hw1 : ∑ e : Fin 2 × Fin 2, (1 - s e.1 e.2) = 1 := by
    rw [Finset.sum_sub_distrib, Fintype.sum_prod_type' s, hs3]
    norm_num
  refine ⟨∑ e : Fin 2 × Fin 2, (1 - s e.1 e.2) • glue q e.1 e.2, ?_, ?_⟩
  · exact (convex_convexHull ℝ _).sum_mem (fun e _ => sub_nonneg.mpr (hs e.1 e.2).2) hw1
      (fun e _ => glue_mem_localSet hq e.1 e.2)
  · intro x y a b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ e : Fin 2 × Fin 2,
        (1 - s e.1 e.2) * (if e = (x, y) then 0 else q x y a b)
          ≤ (1 - s e.1 e.2) * glue q e.1 e.2 x y a b := by
      intro e
      refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr (hs e.1 e.2).2)
      by_cases he : e = (x, y)
      · rw [if_pos he]
        exact glue_nonneg hq e.1 e.2 x y a b
      · rw [if_neg he]
        exact (glue_apply_of_ne hq e.1 e.2 (fun h => he (Prod.ext h.1.symm h.2.symm)) a b).ge
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun e _ => hterm e))
    have hsplit : ∀ e : Fin 2 × Fin 2, (1 - s e.1 e.2) * (if e = (x, y) then 0 else q x y a b)
        = (1 - s e.1 e.2) * q x y a b
          - (if e = (x, y) then (1 - s e.1 e.2) * q x y a b else 0) := by
      intro e
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun e _ => hsplit e), Finset.sum_sub_distrib, ← Finset.sum_mul, hw1,
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    show s x y * q x y a b = 1 * q x y a b - (1 - s x y) * q x y a b
    ring

end

end CGLMPBounds
