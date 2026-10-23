module

public import ThreeCopyQutritWerner.CertificateX2InputNormal

@[expose] public section


/-!
# Input stage: the parity selects as orientation sums

`2 · x2SelS f a b = f a b + f b a` and `2 · x2SelA f a b = f a b - f b a` hold for all `a, b` (the
diagonal included). Three nested selects therefore expand into eight orientation terms; for a function
symmetric under exchanging its two argument triples, the terms with the last site reversed equal the
terms with the first two sites reversed, so `8 · Sel Sel Sel G` is twice a sum of FOUR terms in which
the last site keeps its orientation `(a₂, b₂)`. These are the forms the packed input stage checks:
the run over the last site is one contiguous run of an input-block row.

For the concrete data and any symmetric source `N` of sector 1 or 2:
* `x2EmbedS_eight`: on type-sorted labels, `8 · x2EmbedS` through four key-sum values;
* `x2EmbedA_site1_concrete`, `x2EmbedA_site2_concrete`: `x2EmbedA` when the symmetric label's type lies
  between, or above, the two antisymmetric labels' types (site permutations of the full tensor);
* `x2EmbedA_eight0/1/2`: the corresponding four-term forms with the parity signs.
-/

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner
namespace X2

/-! ### One site -/

theorem x2SelS_two (f : ℕ → ℕ → ℚ) (a b : ℕ) : 2 * x2SelS f a b = f a b + f b a := by
  unfold x2SelS
  split_ifs with h
  · subst h
    ring
  · ring

theorem x2SelA_two (f : ℕ → ℕ → ℚ) (a b : ℕ) : 2 * x2SelA f a b = f a b - f b a := by
  unfold x2SelA
  ring

/-- A symmetric and an antisymmetric select at two different sites commute. -/
theorem x2SelS_SelA_comm (f : ℕ → ℕ → ℕ → ℕ → ℚ) (a b c d : ℕ) :
    x2SelS (fun x y => x2SelA (fun x' y' => f x y x' y') c d) a b =
      x2SelA (fun x' y' => x2SelS (fun x y => f x y x' y') a b) c d := by
  unfold x2SelS x2SelA
  split_ifs <;> ring

/-! ### Three sites: four orientation terms (last site kept) -/

/-- All three selects symmetric. -/
theorem x2Sel8_SSS (G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ)
    (hG : ∀ x0 x1 x2 y0 y1 y2, G x0 x1 x2 y0 y1 y2 = G y0 y1 y2 x0 x1 x2) (a0 b0 a1 b1 a2 b2 : ℕ) :
    8 * x2SelS (fun x0 y0 => x2SelS (fun x1 y1 => x2SelS (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
    2 * (G a0 a1 a2 b0 b1 b2 + G b0 a1 a2 a0 b1 b2 + G a0 b1 a2 b0 a1 b2 + G b0 b1 a2 a0 a1 b2) := by
  have E0 : 2 * x2SelS (fun x0 y0 => x2SelS (fun x1 y1 => x2SelS (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
      x2SelS (fun x1 y1 => x2SelS (fun x2 y2 => G a0 x1 x2 b0 y1 y2) a2 b2) a1 b1 +
        x2SelS (fun x1 y1 => x2SelS (fun x2 y2 => G b0 x1 x2 a0 y1 y2) a2 b2) a1 b1 :=
    x2SelS_two _ a0 b0
  have E1 : ∀ x y, 2 * x2SelS (fun x1 y1 => x2SelS (fun x2 y2 => G x x1 x2 y y1 y2) a2 b2) a1 b1 =
      x2SelS (fun x2 y2 => G x a1 x2 y b1 y2) a2 b2 + x2SelS (fun x2 y2 => G x b1 x2 y a1 y2) a2 b2 :=
    fun x y => x2SelS_two _ a1 b1
  have E2 : ∀ x y u v, 2 * x2SelS (fun x2 y2 => G x u x2 y v y2) a2 b2 =
      G x u a2 y v b2 + G x u b2 y v a2 := fun x y u v => x2SelS_two _ a2 b2
  linear_combination 4 * E0 + 2 * E1 a0 b0 + 2 * E1 b0 a0 + E2 a0 b0 a1 b1 + E2 a0 b0 b1 a1 +
    E2 b0 a0 a1 b1 + E2 b0 a0 b1 a1 + hG a0 a1 b2 b0 b1 a2 + hG a0 b1 b2 b0 a1 a2 +
    hG b0 a1 b2 a0 b1 a2 + hG b0 b1 b2 a0 a1 a2

/-- Symmetric first site, antisymmetric second and third sites. -/
theorem x2Sel8_SAA (G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ)
    (hG : ∀ x0 x1 x2 y0 y1 y2, G x0 x1 x2 y0 y1 y2 = G y0 y1 y2 x0 x1 x2) (a0 b0 a1 b1 a2 b2 : ℕ) :
    8 * x2SelS (fun x0 y0 => x2SelA (fun x1 y1 => x2SelA (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
    2 * (G a0 a1 a2 b0 b1 b2 + G b0 a1 a2 a0 b1 b2 - G a0 b1 a2 b0 a1 b2 - G b0 b1 a2 a0 a1 b2) := by
  have E0 : 2 * x2SelS (fun x0 y0 => x2SelA (fun x1 y1 => x2SelA (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
      x2SelA (fun x1 y1 => x2SelA (fun x2 y2 => G a0 x1 x2 b0 y1 y2) a2 b2) a1 b1 +
        x2SelA (fun x1 y1 => x2SelA (fun x2 y2 => G b0 x1 x2 a0 y1 y2) a2 b2) a1 b1 :=
    x2SelS_two _ a0 b0
  have E1 : ∀ x y, 2 * x2SelA (fun x1 y1 => x2SelA (fun x2 y2 => G x x1 x2 y y1 y2) a2 b2) a1 b1 =
      x2SelA (fun x2 y2 => G x a1 x2 y b1 y2) a2 b2 - x2SelA (fun x2 y2 => G x b1 x2 y a1 y2) a2 b2 :=
    fun x y => x2SelA_two _ a1 b1
  have E2 : ∀ x y u v, 2 * x2SelA (fun x2 y2 => G x u x2 y v y2) a2 b2 =
      G x u a2 y v b2 - G x u b2 y v a2 := fun x y u v => x2SelA_two _ a2 b2
  linear_combination 4 * E0 + 2 * E1 a0 b0 + 2 * E1 b0 a0 + E2 a0 b0 a1 b1 - E2 a0 b0 b1 a1 +
    E2 b0 a0 a1 b1 - E2 b0 a0 b1 a1 - hG a0 a1 b2 b0 b1 a2 + hG a0 b1 b2 b0 a1 a2 -
    hG b0 a1 b2 a0 b1 a2 + hG b0 b1 b2 a0 a1 a2

/-- Antisymmetric first site, symmetric second site, antisymmetric third site. -/
theorem x2Sel8_ASA (G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ)
    (hG : ∀ x0 x1 x2 y0 y1 y2, G x0 x1 x2 y0 y1 y2 = G y0 y1 y2 x0 x1 x2) (a0 b0 a1 b1 a2 b2 : ℕ) :
    8 * x2SelA (fun x0 y0 => x2SelS (fun x1 y1 => x2SelA (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
    2 * (G a0 a1 a2 b0 b1 b2 - G b0 a1 a2 a0 b1 b2 + G a0 b1 a2 b0 a1 b2 - G b0 b1 a2 a0 a1 b2) := by
  have E0 : 2 * x2SelA (fun x0 y0 => x2SelS (fun x1 y1 => x2SelA (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
      x2SelS (fun x1 y1 => x2SelA (fun x2 y2 => G a0 x1 x2 b0 y1 y2) a2 b2) a1 b1 -
        x2SelS (fun x1 y1 => x2SelA (fun x2 y2 => G b0 x1 x2 a0 y1 y2) a2 b2) a1 b1 :=
    x2SelA_two _ a0 b0
  have E1 : ∀ x y, 2 * x2SelS (fun x1 y1 => x2SelA (fun x2 y2 => G x x1 x2 y y1 y2) a2 b2) a1 b1 =
      x2SelA (fun x2 y2 => G x a1 x2 y b1 y2) a2 b2 + x2SelA (fun x2 y2 => G x b1 x2 y a1 y2) a2 b2 :=
    fun x y => x2SelS_two _ a1 b1
  have E2 : ∀ x y u v, 2 * x2SelA (fun x2 y2 => G x u x2 y v y2) a2 b2 =
      G x u a2 y v b2 - G x u b2 y v a2 := fun x y u v => x2SelA_two _ a2 b2
  linear_combination 4 * E0 + 2 * E1 a0 b0 - 2 * E1 b0 a0 + E2 a0 b0 a1 b1 + E2 a0 b0 b1 a1 -
    E2 b0 a0 a1 b1 - E2 b0 a0 b1 a1 - hG a0 a1 b2 b0 b1 a2 - hG a0 b1 b2 b0 a1 a2 +
    hG b0 a1 b2 a0 b1 a2 + hG b0 b1 b2 a0 a1 a2

/-- Antisymmetric first and second sites, symmetric third site. -/
theorem x2Sel8_AAS (G : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ)
    (hG : ∀ x0 x1 x2 y0 y1 y2, G x0 x1 x2 y0 y1 y2 = G y0 y1 y2 x0 x1 x2) (a0 b0 a1 b1 a2 b2 : ℕ) :
    8 * x2SelA (fun x0 y0 => x2SelA (fun x1 y1 => x2SelS (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
    2 * (G a0 a1 a2 b0 b1 b2 - G b0 a1 a2 a0 b1 b2 - G a0 b1 a2 b0 a1 b2 + G b0 b1 a2 a0 a1 b2) := by
  have E0 : 2 * x2SelA (fun x0 y0 => x2SelA (fun x1 y1 => x2SelS (fun x2 y2 =>
      G x0 x1 x2 y0 y1 y2) a2 b2) a1 b1) a0 b0 =
      x2SelA (fun x1 y1 => x2SelS (fun x2 y2 => G a0 x1 x2 b0 y1 y2) a2 b2) a1 b1 -
        x2SelA (fun x1 y1 => x2SelS (fun x2 y2 => G b0 x1 x2 a0 y1 y2) a2 b2) a1 b1 :=
    x2SelA_two _ a0 b0
  have E1 : ∀ x y, 2 * x2SelA (fun x1 y1 => x2SelS (fun x2 y2 => G x x1 x2 y y1 y2) a2 b2) a1 b1 =
      x2SelS (fun x2 y2 => G x a1 x2 y b1 y2) a2 b2 - x2SelS (fun x2 y2 => G x b1 x2 y a1 y2) a2 b2 :=
    fun x y => x2SelA_two _ a1 b1
  have E2 : ∀ x y u v, 2 * x2SelS (fun x2 y2 => G x u x2 y v y2) a2 b2 =
      G x u a2 y v b2 + G x u b2 y v a2 := fun x y u v => x2SelS_two _ a2 b2
  linear_combination 4 * E0 + 2 * E1 a0 b0 - 2 * E1 b0 a0 + E2 a0 b0 a1 b1 - E2 a0 b0 b1 a1 -
    E2 b0 a0 a1 b1 + E2 b0 a0 b1 a1 + hG a0 a1 b2 b0 b1 a2 - hG a0 b1 b2 b0 a1 a2 -
    hG b0 a1 b2 a0 b1 a2 + hG b0 b1 b2 a0 a1 a2

/-! ### Symmetry of the key sums for symmetric sources -/

theorem x2Lookup_symm {p q r : ℕ} (M : Matrix (Fin p × Fin q × Fin r) (Fin p × Fin q × Fin r) ℚ)
    (hM : Mᵀ = M) (a b : Fin 3 → ℕ) : x2Lookup M a b = x2Lookup M b a := by
  unfold x2Lookup
  by_cases ha : a 0 < p ∧ a 1 < q ∧ a 2 < r
  · by_cases hb : b 0 < p ∧ b 1 < q ∧ b 2 < r
    · rw [dif_pos ⟨ha, hb⟩, dif_pos ⟨hb, ha⟩]
      conv_lhs => rw [← hM]
      rfl
    · rw [dif_neg (fun h => hb h.2), dif_neg (fun h => hb h.1)]
  · rw [dif_neg (fun h => ha h.1), dif_neg (fun h => ha h.2)]

theorem x2InputBlock_symm (D : X2Data) (s : Fin 3) (N : X2Blocks s) (k : x2Key s) (hN : (N k)ᵀ = N k) :
    (x2InputBlock D s N k)ᵀ = x2InputBlock D s N k := by
  unfold x2InputBlock
  simp only []
  split_ifs
  · simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hN, Matrix.mul_assoc]
  · simp only [Matrix.transpose_add, Matrix.transpose_zero, Matrix.transpose_mul, Matrix.transpose_transpose,
      hN, Matrix.mul_assoc]

theorem x2KeySum_symm (s : Fin 3) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k) (t : Fin 3 → Fin 8)
    (a b : Fin 3 → ℕ) : x2KeySum s N t a b = x2KeySum s N t b a := by
  unfold x2KeySum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs
  · exact x2Lookup_symm _ (x2InputBlock_symm x2DataConcrete s N k (hN k)) a b
  · rfl

/-! ### The parity embeddings as four-term sums -/

/-- `x2EmbedS` on type-sorted labels: eight times the value is twice the sum of the four key-sum
values with the last site in its label orientation. -/
theorem x2EmbedS_eight (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (l₀ l₁ l₂ : Fin 282) (h01 : (x2SLabel s l₀).1 ≤ (x2SLabel s l₁).1)
    (h12 : (x2SLabel s l₁).1 ≤ (x2SLabel s l₂).1) :
    8 * x2EmbedS x2DataConcrete s N l₀ l₁ l₂ =
      2 * (x2KeySum s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1]
            ![(x2SLabel s l₀).2.1, (x2SLabel s l₁).2.1, (x2SLabel s l₂).2.1]
            ![(x2SLabel s l₀).2.2, (x2SLabel s l₁).2.2, (x2SLabel s l₂).2.2] +
          x2KeySum s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1]
            ![(x2SLabel s l₀).2.2, (x2SLabel s l₁).2.1, (x2SLabel s l₂).2.1]
            ![(x2SLabel s l₀).2.1, (x2SLabel s l₁).2.2, (x2SLabel s l₂).2.2] +
          x2KeySum s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1]
            ![(x2SLabel s l₀).2.1, (x2SLabel s l₁).2.2, (x2SLabel s l₂).2.1]
            ![(x2SLabel s l₀).2.2, (x2SLabel s l₁).2.1, (x2SLabel s l₂).2.2] +
          x2KeySum s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1]
            ![(x2SLabel s l₀).2.2, (x2SLabel s l₁).2.2, (x2SLabel s l₂).2.1]
            ![(x2SLabel s l₀).2.1, (x2SLabel s l₁).2.1, (x2SLabel s l₂).2.2]) := by
  rw [x2EmbedS_sorted_concrete s hs N l₀ l₁ l₂ h01 h12]
  exact x2Sel8_SSS (fun x0 x1 x2 y0 y1 y2 => x2KeySum s N
      ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1] ![x0, x1, x2] ![y0, y1, y2])
    (fun x0 x1 x2 y0 y1 y2 => x2KeySum_symm s N hN _ _ _) _ _ _ _ _ _

theorem x2Perm3_four_vec {α : Type*} (u v w : α) : ![w, u, v] = ![u, v, w] ∘ x2Perm3 4 := by
  funext i
  fin_cases i <;> rfl

/-- `x2EmbedA` when the symmetric label's type lies between the two antisymmetric labels' types: the
canonical arrangement is (first A label, S label, second A label). -/
theorem x2EmbedA_site1_concrete (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (l₀ : Fin 282)
    (l₁ l₂ : Fin 231) (h10 : (x2ALabel s l₁).1 ≤ (x2SLabel s l₀).1)
    (h02 : (x2SLabel s l₀).1 ≤ (x2ALabel s l₂).1) :
    x2EmbedA x2DataConcrete s N l₀ l₁ l₂ =
      x2SelA (fun x₁ y₁ => x2SelS (fun x₀ y₀ => x2SelA (fun x₂ y₂ =>
        x2KeySum s N ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1] ![x₁, x₀, x₂] ![y₁, y₀, y₂])
        (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2) (x2SLabel s l₀).2.1 (x2SLabel s l₀).2.2)
        (x2ALabel s l₁).2.1 (x2ALabel s l₁).2.2 := by
  have ht : x2Sorted ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1] := by
    unfold x2Sorted
    exact ⟨h10, h02⟩
  unfold x2EmbedA
  simp only []
  have hF : ∀ x₀ y₀ x₁ y₁ x₂ y₂ : ℕ,
      x2FullTensor x2DataConcrete s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1]
          ![x₀, x₁, x₂] ![y₀, y₁, y₂] =
        x2KeySum s N ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1] ![x₁, x₀, x₂]
          ![y₁, y₀, y₂] := by
    intro x₀ y₀ x₁ y₁ x₂ y₂
    rw [x2Perm3_two_vec ((x2ALabel s l₁).1) ((x2SLabel s l₀).1), x2Perm3_two_vec x₁ x₀,
      x2Perm3_two_vec y₁ y₀, x2FullTensor_comp]
    unfold x2KeySum
    exact x2FullTensor_sorted_concrete s hs N _ _ _ ht
  simp_rw [hF]
  exact x2SelS_SelA_comm (fun x₀ y₀ x₁ y₁ => x2SelA (fun x₂ y₂ => x2KeySum s N
      ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1] ![x₁, x₀, x₂] ![y₁, y₀, y₂])
      (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2) _ _ _ _

/-- `x2EmbedA` when the symmetric label's type is at least both antisymmetric labels' types: the
canonical arrangement is (first A label, second A label, S label). -/
theorem x2EmbedA_site2_concrete (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (l₀ : Fin 282)
    (l₁ l₂ : Fin 231) (h12 : (x2ALabel s l₁).1 ≤ (x2ALabel s l₂).1)
    (h20 : (x2ALabel s l₂).1 ≤ (x2SLabel s l₀).1) :
    x2EmbedA x2DataConcrete s N l₀ l₁ l₂ =
      x2SelA (fun x₁ y₁ => x2SelA (fun x₂ y₂ => x2SelS (fun x₀ y₀ =>
        x2KeySum s N ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1] ![x₁, x₂, x₀] ![y₁, y₂, y₀])
        (x2SLabel s l₀).2.1 (x2SLabel s l₀).2.2) (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2)
        (x2ALabel s l₁).2.1 (x2ALabel s l₁).2.2 := by
  have ht : x2Sorted ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1] := by
    unfold x2Sorted
    exact ⟨h12, h20⟩
  unfold x2EmbedA
  simp only []
  have hF : ∀ x₀ y₀ x₁ y₁ x₂ y₂ : ℕ,
      x2FullTensor x2DataConcrete s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1]
          ![x₀, x₁, x₂] ![y₀, y₁, y₂] =
        x2KeySum s N ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1] ![x₁, x₂, x₀]
          ![y₁, y₂, y₀] := by
    intro x₀ y₀ x₁ y₁ x₂ y₂
    rw [x2Perm3_four_vec ((x2ALabel s l₁).1) ((x2ALabel s l₂).1), x2Perm3_four_vec x₁ x₂,
      x2Perm3_four_vec y₁ y₂, x2FullTensor_comp]
    unfold x2KeySum
    exact x2FullTensor_sorted_concrete s hs N _ _ _ ht
  simp_rw [hF]
  rw [x2SelS_SelA_comm]
  congr 1
  funext x₁ y₁
  exact x2SelS_SelA_comm (fun x₀ y₀ x₂ y₂ => x2KeySum s N
      ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1] ![x₁, x₂, x₀] ![y₁, y₂, y₀]) _ _ _ _

/-- `x2EmbedA`, symmetric label of the smallest type (canonical arrangement as given). -/
theorem x2EmbedA_eight0 (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (l₀ : Fin 282) (l₁ l₂ : Fin 231) (h01 : (x2SLabel s l₀).1 ≤ (x2ALabel s l₁).1)
    (h12 : (x2ALabel s l₁).1 ≤ (x2ALabel s l₂).1) :
    8 * x2EmbedA x2DataConcrete s N l₀ l₁ l₂ =
      2 * (x2KeySum s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1]
            ![(x2SLabel s l₀).2.1, (x2ALabel s l₁).2.1, (x2ALabel s l₂).2.1]
            ![(x2SLabel s l₀).2.2, (x2ALabel s l₁).2.2, (x2ALabel s l₂).2.2] +
          x2KeySum s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1]
            ![(x2SLabel s l₀).2.2, (x2ALabel s l₁).2.1, (x2ALabel s l₂).2.1]
            ![(x2SLabel s l₀).2.1, (x2ALabel s l₁).2.2, (x2ALabel s l₂).2.2] -
          x2KeySum s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1]
            ![(x2SLabel s l₀).2.1, (x2ALabel s l₁).2.2, (x2ALabel s l₂).2.1]
            ![(x2SLabel s l₀).2.2, (x2ALabel s l₁).2.1, (x2ALabel s l₂).2.2] -
          x2KeySum s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1]
            ![(x2SLabel s l₀).2.2, (x2ALabel s l₁).2.2, (x2ALabel s l₂).2.1]
            ![(x2SLabel s l₀).2.1, (x2ALabel s l₁).2.1, (x2ALabel s l₂).2.2]) := by
  rw [x2EmbedA_sorted_concrete s hs N l₀ l₁ l₂ h01 h12]
  exact x2Sel8_SAA (fun x0 x1 x2 y0 y1 y2 => x2KeySum s N
      ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1] ![x0, x1, x2] ![y0, y1, y2])
    (fun x0 x1 x2 y0 y1 y2 => x2KeySum_symm s N hN _ _ _) _ _ _ _ _ _

/-- `x2EmbedA`, symmetric label's type between the antisymmetric labels' types: canonical
arrangement (A label `l₁`, S label `l₀`, A label `l₂`). -/
theorem x2EmbedA_eight1 (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (l₀ : Fin 282) (l₁ l₂ : Fin 231) (h10 : (x2ALabel s l₁).1 ≤ (x2SLabel s l₀).1)
    (h02 : (x2SLabel s l₀).1 ≤ (x2ALabel s l₂).1) :
    8 * x2EmbedA x2DataConcrete s N l₀ l₁ l₂ =
      2 * (x2KeySum s N ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1]
            ![(x2ALabel s l₁).2.1, (x2SLabel s l₀).2.1, (x2ALabel s l₂).2.1]
            ![(x2ALabel s l₁).2.2, (x2SLabel s l₀).2.2, (x2ALabel s l₂).2.2] -
          x2KeySum s N ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1]
            ![(x2ALabel s l₁).2.2, (x2SLabel s l₀).2.1, (x2ALabel s l₂).2.1]
            ![(x2ALabel s l₁).2.1, (x2SLabel s l₀).2.2, (x2ALabel s l₂).2.2] +
          x2KeySum s N ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1]
            ![(x2ALabel s l₁).2.1, (x2SLabel s l₀).2.2, (x2ALabel s l₂).2.1]
            ![(x2ALabel s l₁).2.2, (x2SLabel s l₀).2.1, (x2ALabel s l₂).2.2] -
          x2KeySum s N ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1]
            ![(x2ALabel s l₁).2.2, (x2SLabel s l₀).2.2, (x2ALabel s l₂).2.1]
            ![(x2ALabel s l₁).2.1, (x2SLabel s l₀).2.1, (x2ALabel s l₂).2.2]) := by
  rw [x2EmbedA_site1_concrete s hs N l₀ l₁ l₂ h10 h02]
  exact x2Sel8_ASA (fun x0 x1 x2 y0 y1 y2 => x2KeySum s N
      ![(x2ALabel s l₁).1, (x2SLabel s l₀).1, (x2ALabel s l₂).1] ![x0, x1, x2] ![y0, y1, y2])
    (fun x0 x1 x2 y0 y1 y2 => x2KeySum_symm s N hN _ _ _) _ _ _ _ _ _

/-- `x2EmbedA`, symmetric label of the largest type: canonical arrangement (A label `l₁`, A label
`l₂`, S label `l₀`). -/
theorem x2EmbedA_eight2 (s : Fin 3) (hs : s = 1 ∨ s = 2) (N : X2Blocks s) (hN : ∀ k, (N k)ᵀ = N k)
    (l₀ : Fin 282) (l₁ l₂ : Fin 231) (h12 : (x2ALabel s l₁).1 ≤ (x2ALabel s l₂).1)
    (h20 : (x2ALabel s l₂).1 ≤ (x2SLabel s l₀).1) :
    8 * x2EmbedA x2DataConcrete s N l₀ l₁ l₂ =
      2 * (x2KeySum s N ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1]
            ![(x2ALabel s l₁).2.1, (x2ALabel s l₂).2.1, (x2SLabel s l₀).2.1]
            ![(x2ALabel s l₁).2.2, (x2ALabel s l₂).2.2, (x2SLabel s l₀).2.2] -
          x2KeySum s N ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1]
            ![(x2ALabel s l₁).2.2, (x2ALabel s l₂).2.1, (x2SLabel s l₀).2.1]
            ![(x2ALabel s l₁).2.1, (x2ALabel s l₂).2.2, (x2SLabel s l₀).2.2] -
          x2KeySum s N ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1]
            ![(x2ALabel s l₁).2.1, (x2ALabel s l₂).2.2, (x2SLabel s l₀).2.1]
            ![(x2ALabel s l₁).2.2, (x2ALabel s l₂).2.1, (x2SLabel s l₀).2.2] +
          x2KeySum s N ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1]
            ![(x2ALabel s l₁).2.2, (x2ALabel s l₂).2.2, (x2SLabel s l₀).2.1]
            ![(x2ALabel s l₁).2.1, (x2ALabel s l₂).2.1, (x2SLabel s l₀).2.2]) := by
  rw [x2EmbedA_site2_concrete s hs N l₀ l₁ l₂ h12 h20]
  exact x2Sel8_AAS (fun x0 x1 x2 y0 y1 y2 => x2KeySum s N
      ![(x2ALabel s l₁).1, (x2ALabel s l₂).1, (x2SLabel s l₀).1] ![x0, x1, x2] ![y0, y1, y2])
    (fun x0 x1 x2 y0 y1 y2 => x2KeySum_symm s N hN _ _ _) _ _ _ _ _ _

end X2
end ThreeCopyQutritWerner
