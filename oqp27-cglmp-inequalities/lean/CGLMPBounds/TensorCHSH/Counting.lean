module

public import CGLMPBounds.Defs.TensorCHSH

@[expose] public section


/-!
# Counting bounds for the tensor-product CHSH witness

This file formalises the counting arguments of Appendix F.2 of the manuscript.

Each party outputs an `m`-bit string. For inputs `x y : Fin 2` and output strings
`s t : Fin m → Bool`, the CHSH error count is `K_{xy}(s,t) = #{j : s_j ⊕ t_j ≠ x·y}`.
A deterministic local assignment is a pair `a b : Fin 2 → Fin m → Bool`: Alice's output string
for each of her inputs and Bob's output string for each of his.

## Main definitions

* `CGLMPBounds.TensorCHSH.errCount`: the CHSH error count `K_{xy}(s,t)`.
* `CGLMPBounds.TensorCHSH.errBit`: the error indicator of a single coordinate.

## Main results

* `CGLMPBounds.TensorCHSH.le_sum_errCount`: (F.6) for every deterministic assignment the four
  error counts sum to at least `m`.
* `CGLMPBounds.TensorCHSH.witness_det_le_two`: if `4 * k < m`, the thresholded witness
  `∑_{x,y} (1[K_{xy} ≤ k] - 1[K_{xy} ≥ m - 3k])` is at most `2` on every deterministic
  assignment.
-/

namespace CGLMPBounds.TensorCHSH

/-! ### Error counts -/

/-- An error count is at most the number `m` of coordinates. -/
theorem errCount_le {m : ℕ} (x y : Fin 2) (s t : Fin m → Bool) : errCount x y s t ≤ m :=
  calc errCount x y s t ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := Finset.card_fin m

/-- `errBit x y p q` is `1` if the output bits `p`, `q` violate the CHSH condition
`p ⊕ q = x·y` for the inputs `x`, `y`, and `0` otherwise. -/
def errBit (x y : Fin 2) (p q : Bool) : ℕ :=
  if xor p q ≠ (decide (x = 1) && decide (y = 1)) then 1 else 0

/-- The error count is the sum over the coordinates of the error indicators. -/
theorem errCount_eq_sum {m : ℕ} (x y : Fin 2) (s t : Fin m → Bool) :
    errCount x y s t = ∑ j : Fin m, errBit x y (s j) (t j) :=
  Finset.card_filter _ _

/-- Per coordinate, at least one of the four input pairs errs: the four parities `p ⊕ r`,
`p ⊕ s`, `q ⊕ r`, `q ⊕ s` XOR to `0`, whereas the four targets `x·y` XOR to `1`. Here `p`, `q`
are Alice's bits for inputs `0`, `1` and `r`, `s` are Bob's. -/
theorem one_le_errBit_add (p q r s : Bool) :
    1 ≤ errBit 0 0 p r + errBit 0 1 p s + (errBit 1 0 q r + errBit 1 1 q s) := by
  cases p <;> cases q <;> cases r <;> cases s <;> decide

/-- A deterministic single-coordinate strategy `α`, `β` errs on at least one of the four
input pairs. -/
theorem one_le_sum_errBit (α β : Fin 2 → Bool) :
    1 ≤ ∑ x : Fin 2, ∑ y : Fin 2, errBit x y (α x) (β y) := by
  simp only [Fin.sum_univ_two]
  exact one_le_errBit_add (α 0) (α 1) (β 0) (β 1)

/-- (F.6) For every deterministic assignment, the four CHSH error counts sum to at least `m`:
every coordinate is an error for at least one of the four input pairs. -/
theorem le_sum_errCount {m : ℕ} (a b : Fin 2 → Fin m → Bool) :
    m ≤ ∑ x : Fin 2, ∑ y : Fin 2, errCount x y (a x) (b y) :=
  calc m = ∑ _j : Fin m, (1 : ℕ) := (Finset.card_fin m).symm.trans (Finset.card_eq_sum_ones _)
    _ ≤ ∑ j : Fin m, ∑ x : Fin 2, ∑ y : Fin 2, errBit x y (a x j) (b y j) :=
      Finset.sum_le_sum fun j _ => one_le_sum_errBit (fun x => a x j) (fun y => b y j)
    _ = ∑ x : Fin 2, ∑ j : Fin m, ∑ y : Fin 2, errBit x y (a x j) (b y j) := Finset.sum_comm
    _ = ∑ x : Fin 2, ∑ y : Fin 2, ∑ j : Fin m, errBit x y (a x j) (b y j) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x : Fin 2, ∑ y : Fin 2, errCount x y (a x) (b y) :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        (errCount_eq_sum x y (a x) (b y)).symm

/-! ### The thresholded witness -/

/-- The three regimes of one summand `1[K ≤ k] - 1[h ≤ K]` of the thresholded witness: it is
at most `1` if `K ≤ k`, it is `0` if `k < K < h`, and it is `-1` if `k < K` and `h ≤ K`. -/
theorem witnessTerm_cases (k h K : ℕ) :
    (K ≤ k ∧ ((if K ≤ k then (1 : ℤ) else 0) - (if h ≤ K then (1 : ℤ) else 0)) ≤ 1) ∨
    (k < K ∧ K < h ∧ ((if K ≤ k then (1 : ℤ) else 0) - (if h ≤ K then (1 : ℤ) else 0)) = 0) ∨
    (k < K ∧ h ≤ K ∧ ((if K ≤ k then (1 : ℤ) else 0) - (if h ≤ K then (1 : ℤ) else 0)) = -1) := by
  split_ifs <;> omega

/-- Arithmetic core of the witness bound. Let four counts `Kᵢ` sum to at least `m`, with
`4 * k < m` and `h + 3 * k ≤ m`. Then they are not all at most `k`, and if three of them are
then the fourth is at least `h`. Hence four summands `wᵢ` in the regimes of
`witnessTerm_cases` sum to at most `2`. -/
theorem sum_four_le_two {m k h : ℕ} (hk : 4 * k < m) (hh : h + 3 * k ≤ m)
    {K₁ K₂ K₃ K₄ : ℕ} {w₁ w₂ w₃ w₄ : ℤ} (hK : m ≤ K₁ + K₂ + (K₃ + K₄))
    (h₁ : (K₁ ≤ k ∧ w₁ ≤ 1) ∨ (k < K₁ ∧ K₁ < h ∧ w₁ = 0) ∨ (k < K₁ ∧ h ≤ K₁ ∧ w₁ = -1))
    (h₂ : (K₂ ≤ k ∧ w₂ ≤ 1) ∨ (k < K₂ ∧ K₂ < h ∧ w₂ = 0) ∨ (k < K₂ ∧ h ≤ K₂ ∧ w₂ = -1))
    (h₃ : (K₃ ≤ k ∧ w₃ ≤ 1) ∨ (k < K₃ ∧ K₃ < h ∧ w₃ = 0) ∨ (k < K₃ ∧ h ≤ K₃ ∧ w₃ = -1))
    (h₄ : (K₄ ≤ k ∧ w₄ ≤ 1) ∨ (k < K₄ ∧ K₄ < h ∧ w₄ = 0) ∨ (k < K₄ ∧ h ≤ K₄ ∧ w₄ = -1)) :
    w₁ + w₂ + (w₃ + w₄) ≤ 2 := by
  omega

/-- The deterministic value of the thresholded witness is at most `2` (i.e. `G_{m,k} ≤ 1/2`
after the `1/4` normalisation): if `4 * k < m` then, for every deterministic assignment,
`∑_{x,y} (1[K_{xy} ≤ k] - 1[K_{xy} ≥ m - 3k]) ≤ 2`. -/
theorem witness_det_le_two {m k : ℕ} (hk : 4 * k < m) (a b : Fin 2 → Fin m → Bool) :
    ∑ x : Fin 2, ∑ y : Fin 2,
      ((if errCount x y (a x) (b y) ≤ k then (1 : ℤ) else 0)
        - (if m - 3 * k ≤ errCount x y (a x) (b y) then (1 : ℤ) else 0)) ≤ 2 := by
  have hh : m - 3 * k + 3 * k ≤ m := by omega
  have hK := le_sum_errCount a b
  simp only [Fin.sum_univ_two] at hK ⊢
  exact sum_four_le_two hk hh hK (witnessTerm_cases _ _ _) (witnessTerm_cases _ _ _)
    (witnessTerm_cases _ _ _) (witnessTerm_cases _ _ _)

end CGLMPBounds.TensorCHSH
