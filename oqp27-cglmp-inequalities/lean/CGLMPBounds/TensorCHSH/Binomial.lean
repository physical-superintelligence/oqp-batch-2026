module

public import CGLMPBounds.Defs.TensorCHSHStatistics
public import CGLMPBounds.Defs.Scenario
public import CGLMPBounds.TensorCHSH.Counting

@[expose] public section


/-!
# The tensor CHSH table and its binomial error statistics

Manuscript locator: Appendix F.2, equation (F.5), `T_m(a,b|x,y) = 2^{-m} (1-r)^{m-K_{xy}} r^{K_{xy}}`
with `r = (2 - √2)/4`, and the statement that under `T_M` each error count is `Bin(M, r)` while
under uniform noise it is `Bin(M, 1/2)`.

`tensorTable m ρ` is the table given by the closed formula with error rate `ρ`; deriving it from
the tensor CHSH measurements on `Φ_{2^m}` is a separate open claim.
-/

namespace CGLMPBounds.TensorCHSH

theorem xor_xor_decide_cancel :
    ∀ p q t : Bool, xor p (xor t (decide (xor p q ≠ t))) = q := by
  decide

theorem xor_xor_ne_iff : ∀ p t s : Bool, (xor p (xor p (xor t s)) ≠ t) ↔ s = true := by
  decide

/-- For a fixed string of Alice and a fixed target parity, Bob's strings correspond bijectively
to the sets of erring coordinates. -/
def errSetEquiv {m : ℕ} (a : Fin m → Bool) (t : Bool) : (Fin m → Bool) ≃ Finset (Fin m) where
  toFun b := Finset.univ.filter fun j => xor (a j) (b j) ≠ t
  invFun S := fun j => xor (a j) (xor t (decide (j ∈ S)))
  left_inv b := by
    funext j
    have h : decide (j ∈ Finset.univ.filter fun j => xor (a j) (b j) ≠ t)
        = decide (xor (a j) (b j) ≠ t) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show xor (a j) (xor t (decide (j ∈ Finset.univ.filter fun j => xor (a j) (b j) ≠ t))) = b j
    rw [h]
    exact xor_xor_decide_cancel _ _ _
  right_inv S := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (xor_xor_ne_iff _ _ _).trans decide_eq_true_iff

/-- Summing a function of the error count over Bob's strings counts strings by Hamming weight. -/
theorem sum_errCount_eq {m : ℕ} (F : ℕ → ℝ) (x y : Fin 2) (a : Fin m → Bool) :
    ∑ b : Fin m → Bool, F (errCount x y a b)
      = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * F j := by
  have h0 : (Finset.univ : Finset (Fin m)).powerset = Finset.univ := by
    ext S
    simp
  have h1 : ∑ b : Fin m → Bool, F (errCount x y a b) = ∑ S : Finset (Fin m), F S.card :=
    Fintype.sum_equiv (errSetEquiv a (decide (x = 1) && decide (y = 1))) _ _ (fun _ => rfl)
  rw [h1, ← h0, Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]

noncomputable section

/-- In each context the error count of `tensorTable m ρ` is binomial with parameters `(m, ρ)`. -/
theorem sum_sum_tensorTable {m : ℕ} (ρ : ℝ) (g : ℕ → ℝ) (x y : Fin 2) :
    ∑ a : Fin m → Bool, ∑ b : Fin m → Bool, g (errCount x y a b) * tensorTable m ρ x y a b
      = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (g j * ((1 - ρ) ^ (m - j) * ρ ^ j)) := by
  have inner : ∀ a : Fin m → Bool,
      ∑ b : Fin m → Bool, g (errCount x y a b) * tensorTable m ρ x y a b
        = (1 / 2 : ℝ) ^ m * ∑ j ∈ Finset.range (m + 1),
            (m.choose j : ℝ) * (g j * ((1 - ρ) ^ (m - j) * ρ ^ j)) := by
    intro a
    have e : ∀ b : Fin m → Bool, g (errCount x y a b) * tensorTable m ρ x y a b
        = (1 / 2 : ℝ) ^ m * (g (errCount x y a b)
            * ((1 - ρ) ^ (m - errCount x y a b) * ρ ^ errCount x y a b)) := by
      intro b
      simp only [tensorTable]
      ring
    simp only [e]
    rw [← Finset.mul_sum]
    exact congrArg (fun z => (1 / 2 : ℝ) ^ m * z)
      (sum_errCount_eq (fun j => g j * ((1 - ρ) ^ (m - j) * ρ ^ j)) x y a)
  simp only [inner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc]
  have h2 : ((2 ^ m : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m = 1 := by
    push_cast
    rw [← mul_pow]
    norm_num
  rw [h2, one_mul]

/-- At error rate `1/2` the closed formula is the uniform table. -/
theorem tensorTable_half (m : ℕ) :
    tensorTable m (1 / 2) = uniformTable (Fin m → Bool) (Fin m → Bool) := by
  funext x y a b
  have hK : errCount x y a b ≤ m := errCount_le x y a b
  have h1 : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  simp only [tensorTable, uniformTable, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [h1, ← pow_add, Nat.sub_add_cancel hK]
  push_cast
  rw [one_div, one_div, inv_pow, ← mul_inv]

end

end CGLMPBounds.TensorCHSH
