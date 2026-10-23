module

public import ThreeCopyQutritWerner.CertificateX2Reduced

@[expose] public section


/-!
# Input stage: the input blocks of Gram-plus-correction sources

For a source block `N b = A Aᵀ + K C Kᵀ` (the corrected sources: `A = F / 2^80` with the trial factor
`F = K Z`, plus `K C Kᵀ` with the exact correction `C = Cnum / den_c` on the 8 corrected blocks and
`C = 0` elsewhere), the bridge's input block is
`x2InputBlock = (GJ A)(GJ A)ᵀ + (GJ K) C (GJ K)ᵀ` (+ the partner terms of S3 degree 2),
`GJ = x2GramKron · image`. The kernel then needs the factors `V = GJ A` (and `GJ K`) only, never
the input blocks themselves (1.3e8 entries per sector).
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-- The matrix `GJ` of a source block (Gram Kronecker product times the image), over ℚ. -/
noncomputable def x2GJ (D : X2Data) (s : Fin 3) (b : x2Key s) : Matrix (x2Amb s b) (x2Col s b) ℚ :=
  (x2GramKron s b * D.image s b).map (Int.cast : ℤ → ℚ)

theorem x2Get3_mul {p q r : ℕ} {ι κ : Type*} [Fintype κ] (V : Matrix (Fin p × Fin q × Fin r) κ ℚ)
    (A : Matrix κ ι ℚ) (i j k : ℕ) (c : ι) :
    x2Get3 (V * A) i j k c = ∑ d, x2Get3 V i j k d * A d c := by
  unfold x2Get3
  split_ifs with h
  · rw [Matrix.mul_apply]
  · simp

/-- The partner map acts on rows, so it commutes with right multiplication. -/
theorem x2Partner_mul {p q r : ℕ} {ι κ : Type*} [Fintype κ] (V : Matrix (Fin p × Fin q × Fin r) κ ℚ)
    (A : Matrix κ ι ℚ) : x2Partner (V * A) = x2Partner V * A := by
  ext x c
  simp only [x2Partner, Matrix.of_apply, Matrix.mul_apply, x2Get3_mul, sub_mul, Finset.sum_sub_distrib]

/-- Input block of a source block of the form `A Aᵀ + K C Kᵀ`. -/
theorem x2InputBlock_eq (D : X2Data) (s : Fin 3) (N : X2Blocks s) (b : x2Key s) {n m : ℕ}
    (A : Matrix (x2Col s b) (Fin n) ℚ) (K : Matrix (x2Col s b) (Fin m) ℚ) (C : Matrix (Fin m) (Fin m) ℚ)
    (hN : N b = A * Aᵀ + K * C * Kᵀ) :
    x2InputBlock D s N b =
      (x2GJ D s b * A) * (x2GJ D s b * A)ᵀ + (x2GJ D s b * K) * C * (x2GJ D s b * K)ᵀ +
        if x2KeyDegree s b = 2 then
          (1 / 3 : ℚ) • (x2Partner (x2GJ D s b * A) * (x2Partner (x2GJ D s b * A))ᵀ +
            x2Partner (x2GJ D s b * K) * C * (x2Partner (x2GJ D s b * K))ᵀ)
        else 0 := by
  unfold x2InputBlock x2GJ
  simp only []
  rw [hN, x2Partner_mul, x2Partner_mul]
  split_ifs
  · simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  · simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Entries of the input block of a degree-1 source block `A Aᵀ + K C Kᵀ`, through `V = GJ A`,
`U = GJ K`. -/
theorem x2InputBlock_apply (D : X2Data) (s : Fin 3) (N : X2Blocks s) (b : x2Key s) {n m : ℕ}
    (A : Matrix (x2Col s b) (Fin n) ℚ) (K : Matrix (x2Col s b) (Fin m) ℚ) (C : Matrix (Fin m) (Fin m) ℚ)
    (hN : N b = A * Aᵀ + K * C * Kᵀ) (hdeg : x2KeyDegree s b ≠ 2) (x y : x2Amb s b) :
    x2InputBlock D s N b x y =
      ∑ c, (x2GJ D s b * A) x c * (x2GJ D s b * A) y c +
        ∑ c, ∑ c', (x2GJ D s b * K) x c * C c c' * (x2GJ D s b * K) y c' := by
  rw [x2InputBlock_eq D s N b A K C hN, if_neg hdeg, add_zero, Matrix.add_apply]
  have h1 : ((x2GJ D s b * A) * (x2GJ D s b * A)ᵀ) x y =
      ∑ c, (x2GJ D s b * A) x c * (x2GJ D s b * A) y c := by
    rw [Matrix.mul_apply]
    rfl
  have h2 : ((x2GJ D s b * K) * C * (x2GJ D s b * K)ᵀ) x y =
      ∑ c, ∑ c', (x2GJ D s b * K) x c * C c c' * (x2GJ D s b * K) y c' := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [h1, h2]

/-! ### Natural-coordinate lookups and site-permutation invariance -/

theorem x2gram_apply {α : Type*} [Fintype α] {n m : ℕ} (V : Matrix α (Fin n) ℚ) (U : Matrix α (Fin m) ℚ)
    (C : Matrix (Fin m) (Fin m) ℚ) (x y : α) :
    (V * Vᵀ + U * C * Uᵀ) x y = ∑ c, V x c * V y c + ∑ c, ∑ c', U x c * C c c' * U y c' := by
  rw [Matrix.add_apply]
  have h1 : (V * Vᵀ) x y = ∑ c, V x c * V y c := by
    rw [Matrix.mul_apply]
    rfl
  have h2 : (U * C * Uᵀ) x y = ∑ c, ∑ c', U x c * C c c' * U y c' := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [h1, h2]

/-- `x2Lookup` of `V Vᵀ + U C Uᵀ` through the natural-coordinate lookups of `V` and `U`. -/
theorem x2Lookup_gram {p q r n m : ℕ} (V : Matrix (Fin p × Fin q × Fin r) (Fin n) ℚ)
    (U : Matrix (Fin p × Fin q × Fin r) (Fin m) ℚ) (C : Matrix (Fin m) (Fin m) ℚ) (a b : Fin 3 → ℕ) :
    x2Lookup (V * Vᵀ + U * C * Uᵀ) a b =
      ∑ c, x2Get3 V (a 0) (a 1) (a 2) c * x2Get3 V (b 0) (b 1) (b 2) c +
        ∑ c, ∑ c', x2Get3 U (a 0) (a 1) (a 2) c * C c c' * x2Get3 U (b 0) (b 1) (b 2) c' := by
  unfold x2Lookup x2Get3
  by_cases ha : a 0 < p ∧ a 1 < q ∧ a 2 < r
  · by_cases hb : b 0 < p ∧ b 1 < q ∧ b 2 < r
    · rw [dif_pos ⟨ha, hb⟩, x2gram_apply]
      simp only [dif_pos ha, dif_pos hb]
    · rw [dif_neg (fun h => hb h.2)]
      simp [dif_neg hb]
  · rw [dif_neg (fun h => ha h.1)]
    simp [dif_neg ha]

/-- If the lookups of `V` and `U` change by a common sign `ε` (`ε² = 1`) under a site permutation `π`,
`x2Lookup (V Vᵀ + U C Uᵀ)` is invariant under `π` applied to both arguments. -/
theorem x2Lookup_gram_inv {p q r n m : ℕ} (V : Matrix (Fin p × Fin q × Fin r) (Fin n) ℚ)
    (U : Matrix (Fin p × Fin q × Fin r) (Fin m) ℚ) (C : Matrix (Fin m) (Fin m) ℚ) (π : Fin 3 → Fin 3)
    (ε : ℚ) (hε : ε * ε = 1)
    (hV : ∀ (a : Fin 3 → ℕ) (c : Fin n),
      x2Get3 V (a (π 0)) (a (π 1)) (a (π 2)) c = ε * x2Get3 V (a 0) (a 1) (a 2) c)
    (hU : ∀ (a : Fin 3 → ℕ) (c : Fin m),
      x2Get3 U (a (π 0)) (a (π 1)) (a (π 2)) c = ε * x2Get3 U (a 0) (a 1) (a 2) c)
    (a b : Fin 3 → ℕ) :
    x2Lookup (V * Vᵀ + U * C * Uᵀ) (a ∘ π) (b ∘ π) = x2Lookup (V * Vᵀ + U * C * Uᵀ) a b := by
  rw [x2Lookup_gram, x2Lookup_gram]
  simp only [Function.comp_apply, hV, hU]
  have e1 : ∑ c, ε * x2Get3 V (a 0) (a 1) (a 2) c * (ε * x2Get3 V (b 0) (b 1) (b 2) c) =
      ∑ c, x2Get3 V (a 0) (a 1) (a 2) c * x2Get3 V (b 0) (b 1) (b 2) c := by
    apply Finset.sum_congr rfl
    intro c _
    linear_combination (x2Get3 V (a 0) (a 1) (a 2) c * x2Get3 V (b 0) (b 1) (b 2) c) * hε
  have e2 : ∑ c, ∑ c', ε * x2Get3 U (a 0) (a 1) (a 2) c * C c c' * (ε * x2Get3 U (b 0) (b 1) (b 2) c') =
      ∑ c, ∑ c', x2Get3 U (a 0) (a 1) (a 2) c * C c c' * x2Get3 U (b 0) (b 1) (b 2) c' := by
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro c' _
    linear_combination (x2Get3 U (a 0) (a 1) (a 2) c * C c c' * x2Get3 U (b 0) (b 1) (b 2) c') * hε
  rw [e1, e2]

/-- A sign law of the lookups of `G` passes to `G * A` for any `A`. -/
theorem x2Get3_mul_sign {p q r : ℕ} {κ ι : Type*} [Fintype κ] (G : Matrix (Fin p × Fin q × Fin r) κ ℚ)
    (A : Matrix κ ι ℚ) (π : Fin 3 → Fin 3) (ε : ℚ)
    (hG : ∀ (a : Fin 3 → ℕ) (d : κ), x2Get3 G (a (π 0)) (a (π 1)) (a (π 2)) d = ε * x2Get3 G (a 0) (a 1) (a 2) d)
    (a : Fin 3 → ℕ) (c : ι) :
    x2Get3 (G * A) (a (π 0)) (a (π 1)) (a (π 2)) c = ε * x2Get3 (G * A) (a 0) (a 1) (a 2) c := by
  rw [x2Get3_mul, x2Get3_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [hG a d]
  ring

/-! ### The sign law of `GJ` from the sign law of the image (swap of the first two sites) -/

/-- Natural lookup of the local Gram rows. -/
def x2gl (s : Fin 3) (t : Fin 8) (i j : ℕ) : ℤ := ((x2GramRows s t).getD i []).getD j 0

theorem x2GramRows_length : ∀ s : Fin 3, ∀ t : Fin 8, (x2GramRows s t).length = x2Mult s t := by
  decide

theorem x2gl_out (s : Fin 3) (t : Fin 8) (i j : ℕ) (hi : x2Mult s t ≤ i) : x2gl s t i j = 0 := by
  unfold x2gl
  have h : (x2GramRows s t).length ≤ i := by rw [x2GramRows_length]; exact hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- `GJ` at natural coordinates, as a triple sum over the units of the three sites. -/
theorem x2GJ_get3 (D : X2Data) (s : Fin 3) (k : x2Key s) (a0 a1 a2 : ℕ) (d : x2Col s k) :
    x2Get3 (x2GJ D s k) a0 a1 a2 d =
      ∑ y0 ∈ Finset.range (x2KeyMult s k 0), ∑ y1 ∈ Finset.range (x2KeyMult s k 1),
        ∑ y2 ∈ Finset.range (x2KeyMult s k 2),
          ((x2gl s (x2KeyTypes s k 0) a0 y0 * (x2gl s (x2KeyTypes s k 1) a1 y1 *
              x2gl s (x2KeyTypes s k 2) a2 y2) : ℤ) : ℚ) *
            x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d := by
  have hJ : ∀ (y0 : Fin (x2KeyMult s k 0)) (y1 : Fin (x2KeyMult s k 1)) (y2 : Fin (x2KeyMult s k 2)),
      x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d = ((D.image s k (y0, y1, y2) d : ℤ) : ℚ) := by
    intro y0 y1 y2
    unfold x2Get3
    rw [dif_pos ⟨y0.isLt, y1.isLt, y2.isLt⟩]
    rfl
  simp only [← Fin.sum_univ_eq_sum_range (fun y0 => ∑ y1 ∈ Finset.range (x2KeyMult s k 1), _),
    ← Fin.sum_univ_eq_sum_range (fun y1 => ∑ y2 ∈ Finset.range (x2KeyMult s k 2), _),
    ← Fin.sum_univ_eq_sum_range (fun y2 => _), hJ]
  unfold x2Get3
  split_ifs with h
  · simp only [x2GJ, Matrix.map_apply, Matrix.mul_apply, x2GramKron, Matrix.kroneckerMap_apply, x2Gram,
      Matrix.of_apply, Int.cast_sum, Int.cast_mul, Fintype.sum_prod_type, x2gl]
  · symm
    apply Finset.sum_eq_zero
    intro y0 _
    apply Finset.sum_eq_zero
    intro y1 _
    apply Finset.sum_eq_zero
    intro y2 _
    have hout : x2Mult s (x2KeyTypes s k 0) ≤ a0 ∨ x2Mult s (x2KeyTypes s k 1) ≤ a1 ∨
        x2Mult s (x2KeyTypes s k 2) ≤ a2 := by
      by_contra hc
      push_neg at hc
      exact h ⟨hc.1, hc.2.1, hc.2.2⟩
    rcases hout with h0 | h1 | h2
    · rw [x2gl_out s _ a0 y0 h0]
      simp
    · rw [x2gl_out s _ a1 y1 h1]
      simp
    · rw [x2gl_out s _ a2 y2 h2]
      simp

/-- Sign law of `GJ` under the swap of the first two sites (equal types), from that of the image. -/
theorem x2GJ_swap01 (D : X2Data) (s : Fin 3) (k : x2Key s) (ε : ℚ)
    (ht : x2KeyTypes s k 0 = x2KeyTypes s k 1)
    (hJ : ∀ (y0 y1 y2 : ℕ) (d : x2Col s k), x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y1 y0 y2 d =
      ε * x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d)
    (a0 a1 a2 : ℕ) (d : x2Col s k) :
    x2Get3 (x2GJ D s k) a1 a0 a2 d = ε * x2Get3 (x2GJ D s k) a0 a1 a2 d := by
  have hm : x2KeyMult s k 0 = x2KeyMult s k 1 := by
    show x2Mult s (x2KeyTypes s k 0) = x2Mult s (x2KeyTypes s k 1)
    rw [ht]
  have hg : ∀ i j : ℕ, x2gl s (x2KeyTypes s k 0) i j = x2gl s (x2KeyTypes s k 1) i j := by
    intro i j
    rw [ht]
  rw [x2GJ_get3, x2GJ_get3, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr (by rw [hm]) (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr (by rw [hm]) (fun v _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [hJ u v w d, hg a1 v, hg a0 u]
  push_cast
  ring

/-- Sign law of `GJ` under the swap of the last two sites (equal types), from that of the image. -/
theorem x2GJ_swap12 (D : X2Data) (s : Fin 3) (k : x2Key s) (ε : ℚ)
    (ht : x2KeyTypes s k 1 = x2KeyTypes s k 2)
    (hJ : ∀ (y0 y1 y2 : ℕ) (d : x2Col s k), x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y2 y1 d =
      ε * x2Get3 ((D.image s k).map (Int.cast : ℤ → ℚ)) y0 y1 y2 d)
    (a0 a1 a2 : ℕ) (d : x2Col s k) :
    x2Get3 (x2GJ D s k) a0 a2 a1 d = ε * x2Get3 (x2GJ D s k) a0 a1 a2 d := by
  have hm : x2KeyMult s k 1 = x2KeyMult s k 2 := by
    show x2Mult s (x2KeyTypes s k 1) = x2Mult s (x2KeyTypes s k 2)
    rw [ht]
  have hg : ∀ i j : ℕ, x2gl s (x2KeyTypes s k 1) i j = x2gl s (x2KeyTypes s k 2) i j := by
    intro i j
    rw [ht]
  rw [x2GJ_get3, x2GJ_get3, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr (by rw [hm]) (fun v _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr (by rw [hm]) (fun w _ => ?_)
  rw [hJ u v w d, hg a2 w, hg a1 v]
  push_cast
  ring

end X2
end ThreeCopyQutritWerner
