module

public import ThreeCopyQutritWerner.CertificateX2Reduced

@[expose] public section


/-!
# Input stage, step 1: site-permutation invariance of the full tensor

`x2FullTensor D s N t a b` averages the canonical input blocks over the site permutations that
sort the type arrangement `t`. Reindexing that average by a site permutation `σ` gives
`x2FullTensor D s N (t ∘ σ) (a ∘ σ) (b ∘ σ) = x2FullTensor D s N t a b` for any data: the bridge's
source tensors are invariant under permutations of the three sites, which lets the input stage
check symmetry-reduced data only.
-/

open scoped BigOperators

namespace ThreeCopyQutritWerner
namespace X2

/-- Composition table of the six site permutations: `x2Perm3 (x2PermMul q p) = x2Perm3 q ∘ x2Perm3 p`. -/
def x2PermMul (q p : Fin 6) : Fin 6 :=
  (![![0, 1, 2, 3, 4, 5], ![1, 0, 4, 5, 2, 3], ![2, 3, 0, 1, 5, 4], ![3, 2, 5, 4, 0, 1],
    ![4, 5, 1, 0, 3, 2], ![5, 4, 3, 2, 1, 0]] : Fin 6 → Fin 6 → Fin 6) q p

theorem x2PermMul_spec : ∀ q p : Fin 6, x2Perm3 (x2PermMul q p) = x2Perm3 q ∘ x2Perm3 p := by
  decide +kernel

theorem x2PermMul_bij (q : Fin 6) : Function.Bijective (x2PermMul q) := by
  revert q
  decide +kernel

/-- Left multiplication by a site permutation, as an equivalence of the permutation indices. -/
noncomputable def x2PermMulEquiv (q : Fin 6) : Fin 6 ≃ Fin 6 :=
  Equiv.ofBijective (x2PermMul q) (x2PermMul_bij q)

theorem x2ArrangeCount_comp (t τ : Fin 3 → Fin 8) (q : Fin 6) :
    x2ArrangeCount (t ∘ x2Perm3 q) τ = x2ArrangeCount t τ := by
  unfold x2ArrangeCount
  have h : ∀ p : Fin 6, (t ∘ x2Perm3 q) ∘ x2Perm3 p = t ∘ x2Perm3 (x2PermMul q p) := by
    intro p
    rw [x2PermMul_spec, Function.comp_assoc]
  rw [Finset.card_filter, Finset.card_filter]
  simp_rw [h]
  exact Equiv.sum_comp (x2PermMulEquiv q) (fun p => if t ∘ x2Perm3 p = τ then 1 else 0)

/-- Site-permutation invariance of the full tensor. -/
theorem x2FullTensor_comp (D : X2Data) (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8)
    (a b : Fin 3 → ℕ) (q : Fin 6) :
    x2FullTensor D s N (t ∘ x2Perm3 q) (a ∘ x2Perm3 q) (b ∘ x2Perm3 q) = x2FullTensor D s N t a b := by
  unfold x2FullTensor
  apply Finset.sum_congr rfl
  intro k _
  have ht : ∀ p : Fin 6, (t ∘ x2Perm3 q) ∘ x2Perm3 p = t ∘ x2Perm3 (x2PermMul q p) := by
    intro p
    rw [x2PermMul_spec, Function.comp_assoc]
  have ha : ∀ p : Fin 6, (a ∘ x2Perm3 q) ∘ x2Perm3 p = a ∘ x2Perm3 (x2PermMul q p) := by
    intro p
    rw [x2PermMul_spec, Function.comp_assoc]
  have hb : ∀ p : Fin 6, (b ∘ x2Perm3 q) ∘ x2Perm3 p = b ∘ x2Perm3 (x2PermMul q p) := by
    intro p
    rw [x2PermMul_spec, Function.comp_assoc]
  simp_rw [ht, ha, hb, x2ArrangeCount_comp]
  exact Equiv.sum_comp (x2PermMulEquiv q) (fun p =>
    if t ∘ x2Perm3 p = x2KeyTypes s k then
      ((x2ArrangeCount t (x2KeyTypes s k) : ℚ))⁻¹ *
        x2Lookup (x2InputBlock D s N k) (a ∘ x2Perm3 p) (b ∘ x2Perm3 p)
    else 0)

/-! ### Consequences for the parity embeddings -/

/-- Parity selects at two different sites commute. -/
theorem x2SelS_comm (f : ℕ → ℕ → ℕ → ℕ → ℚ) (a b c d : ℕ) :
    x2SelS (fun x y => x2SelS (fun x' y' => f x y x' y') c d) a b =
      x2SelS (fun x' y' => x2SelS (fun x y => f x y x' y') a b) c d := by
  unfold x2SelS
  split_ifs <;> ring

theorem x2Perm3_two_vec {α : Type*} (u v w : α) : ![v, u, w] = ![u, v, w] ∘ x2Perm3 2 := by
  funext i
  fin_cases i <;> rfl

theorem x2Perm3_one_vec {α : Type*} (u v w : α) : ![u, w, v] = ![u, v, w] ∘ x2Perm3 1 := by
  funext i
  fin_cases i <;> rfl

/-- `x2EmbedS` is symmetric in its first two labels. -/
theorem x2EmbedS_swap01 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (l₀ l₁ l₂ : Fin 282) :
    x2EmbedS D s N l₁ l₀ l₂ = x2EmbedS D s N l₀ l₁ l₂ := by
  unfold x2EmbedS
  simp only []
  have h : ∀ x₀ y₀ x₁ y₁ x₂ y₂ : ℕ,
      x2FullTensor D s N ![(x2SLabel s l₁).1, (x2SLabel s l₀).1, (x2SLabel s l₂).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂] =
        x2FullTensor D s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1] ![x₁, x₀, x₂] ![y₁, y₀, y₂] := by
    intro x₀ y₀ x₁ y₁ x₂ y₂
    rw [x2Perm3_two_vec (x2SLabel s l₀).1, x2Perm3_two_vec x₁, x2Perm3_two_vec y₁, x2FullTensor_comp]
  simp_rw [h]
  exact x2SelS_comm (fun x₁ y₁ x₀ y₀ => x2SelS (fun x₂ y₂ =>
      x2FullTensor D s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂])
      (x2SLabel s l₂).2.1 (x2SLabel s l₂).2.2)
    (x2SLabel s l₁).2.1 (x2SLabel s l₁).2.2 (x2SLabel s l₀).2.1 (x2SLabel s l₀).2.2

/-- `x2EmbedS` is symmetric in its last two labels. -/
theorem x2EmbedS_swap12 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (l₀ l₁ l₂ : Fin 282) :
    x2EmbedS D s N l₀ l₂ l₁ = x2EmbedS D s N l₀ l₁ l₂ := by
  unfold x2EmbedS
  simp only []
  have h : ∀ x₀ y₀ x₁ y₁ x₂ y₂ : ℕ,
      x2FullTensor D s N ![(x2SLabel s l₀).1, (x2SLabel s l₂).1, (x2SLabel s l₁).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂] =
        x2FullTensor D s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1] ![x₀, x₂, x₁] ![y₀, y₂, y₁] := by
    intro x₀ y₀ x₁ y₁ x₂ y₂
    rw [x2Perm3_one_vec (x2SLabel s l₀).1 (x2SLabel s l₁).1, x2Perm3_one_vec x₀ x₂, x2Perm3_one_vec y₀ y₂,
      x2FullTensor_comp]
  simp_rw [h]
  congr 1
  funext x₀ y₀
  exact x2SelS_comm (fun x₂ y₂ x₁ y₁ =>
      x2FullTensor D s N ![(x2SLabel s l₀).1, (x2SLabel s l₁).1, (x2SLabel s l₂).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂])
    (x2SLabel s l₂).2.1 (x2SLabel s l₂).2.2 (x2SLabel s l₁).2.1 (x2SLabel s l₁).2.2

/-- Antisymmetric selects at two different sites commute. -/
theorem x2SelA_comm (f : ℕ → ℕ → ℕ → ℕ → ℚ) (a b c d : ℕ) :
    x2SelA (fun x y => x2SelA (fun x' y' => f x y x' y') c d) a b =
      x2SelA (fun x' y' => x2SelA (fun x y => f x y x' y') a b) c d := by
  unfold x2SelA
  ring

/-- `x2EmbedA` is symmetric in its two A-labels. -/
theorem x2EmbedA_swap12 (D : X2Data) (s : Fin 3) (N : X2Blocks s) (l₀ : Fin 282) (l₁ l₂ : Fin 231) :
    x2EmbedA D s N l₀ l₂ l₁ = x2EmbedA D s N l₀ l₁ l₂ := by
  unfold x2EmbedA
  simp only []
  have h : ∀ x₀ y₀ x₁ y₁ x₂ y₂ : ℕ,
      x2FullTensor D s N ![(x2SLabel s l₀).1, (x2ALabel s l₂).1, (x2ALabel s l₁).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂] =
        x2FullTensor D s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1] ![x₀, x₂, x₁] ![y₀, y₂, y₁] := by
    intro x₀ y₀ x₁ y₁ x₂ y₂
    rw [x2Perm3_one_vec (x2SLabel s l₀).1 (x2ALabel s l₁).1, x2Perm3_one_vec x₀ x₂, x2Perm3_one_vec y₀ y₂,
      x2FullTensor_comp]
  simp_rw [h]
  congr 1
  funext x₀ y₀
  exact x2SelA_comm (fun x₂ y₂ x₁ y₁ =>
      x2FullTensor D s N ![(x2SLabel s l₀).1, (x2ALabel s l₁).1, (x2ALabel s l₂).1] ![x₀, x₁, x₂] ![y₀, y₁, y₂])
    (x2ALabel s l₂).2.1 (x2ALabel s l₂).2.2 (x2ALabel s l₁).2.1 (x2ALabel s l₁).2.2

/-! ### Sorted type triples: the average over arrangements collapses -/

/-- A type triple in nondecreasing order. -/
def x2Sorted (t : Fin 3 → Fin 8) : Prop := t 0 ≤ t 1 ∧ t 1 ≤ t 2

/-- A rearrangement of a sorted triple that is again sorted is the triple itself. -/
theorem x2_sorted_perm (t u : Fin 3 → Fin 8) (p : Fin 6) (ht : x2Sorted t) (hu : x2Sorted u)
    (h : t ∘ x2Perm3 p = u) : u = t := by
  obtain ⟨h01, h12⟩ := ht
  obtain ⟨u01, u12⟩ := hu
  subst h
  rw [Fin.le_iff_val_le_val] at h01 h12 u01 u12
  funext i
  apply Fin.ext
  fin_cases p <;> fin_cases i <;>
    simp [x2Perm3, Function.comp] at u01 u12 ⊢ <;> omega

/-- On a sorted type triple, if the input blocks of the keys of that triple are invariant under the
site permutations that fix the triple, the full tensor is the plain sum of their entries. -/
theorem x2FullTensor_sorted (D : X2Data) (s : Fin 3) (N : X2Blocks s) (t : Fin 3 → Fin 8)
    (a b : Fin 3 → ℕ) (ht : x2Sorted t) (hkeys : ∀ k : x2Key s, x2Sorted (x2KeyTypes s k))
    (hinv : ∀ k : x2Key s, x2KeyTypes s k = t → ∀ p : Fin 6, t ∘ x2Perm3 p = t →
      x2Lookup (x2InputBlock D s N k) (a ∘ x2Perm3 p) (b ∘ x2Perm3 p) =
        x2Lookup (x2InputBlock D s N k) a b) :
    x2FullTensor D s N t a b =
      ∑ k : x2Key s, if x2KeyTypes s k = t then x2Lookup (x2InputBlock D s N k) a b else 0 := by
  unfold x2FullTensor
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : x2KeyTypes s k = t
  · rw [if_pos hk, hk]
    have h1 : ∀ p ∈ (Finset.univ : Finset (Fin 6)),
        (if t ∘ x2Perm3 p = t then ((x2ArrangeCount t t : ℕ) : ℚ)⁻¹ *
            x2Lookup (x2InputBlock D s N k) (a ∘ x2Perm3 p) (b ∘ x2Perm3 p) else 0) =
          (if t ∘ x2Perm3 p = t then ((x2ArrangeCount t t : ℕ) : ℚ)⁻¹ *
            x2Lookup (x2InputBlock D s N k) a b else 0) := by
      intro p _
      split_ifs with hp
      · rw [hinv k hk p hp]
      · rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul]
    have hc : x2ArrangeCount t t = (Finset.univ.filter (fun p : Fin 6 => t ∘ x2Perm3 p = t)).card := rfl
    have hpos : 0 < x2ArrangeCount t t := by
      rw [hc]
      apply Finset.card_pos.mpr
      refine ⟨0, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      funext i
      fin_cases i <;> rfl
    rw [← hc]
    have hne : ((x2ArrangeCount t t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    intro hp
    exact hk (x2_sorted_perm t (x2KeyTypes s k) p ht (hkeys k) hp)

end X2
end ThreeCopyQutritWerner
