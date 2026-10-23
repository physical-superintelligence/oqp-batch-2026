module

public import CGLMPBounds.Noise.HalfNoise

@[expose] public section


/-!
# The uniform table is Bell-local

A special case of (F.4): the uniform table has uniform marginals and equals its own half-noise
mixture.
-/

namespace CGLMPBounds

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem uniformTable_mem_localSet [Nonempty α] [Nonempty β] :
    uniformTable α β ∈ localSet α β := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hn' : (Fintype.card α : ℝ) * (1 / (Fintype.card α : ℝ)) = 1 := by
    rw [mul_one_div, div_self hn]
  have hm' : (Fintype.card β : ℝ) * (1 / (Fintype.card β : ℝ)) = 1 := by
    rw [mul_one_div, div_self hm]
  have h0 : ∀ (x y : Fin 2) (a : α) (b : β), 0 ≤ uniformTable α β x y a b := by
    intro x y a b
    show (0 : ℝ) ≤ 1 / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ))
    exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hA : ∀ (x y : Fin 2) (a : α),
      ∑ b : β, uniformTable α β x y a b = 1 / (Fintype.card α : ℝ) := by
    intro x y a
    show ∑ _b : β, (1 / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))
      = 1 / (Fintype.card α : ℝ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination (1 / (Fintype.card α : ℝ)) * hm'
  have hB : ∀ (x y : Fin 2) (b : β),
      ∑ a : α, uniformTable α β x y a b = 1 / (Fintype.card β : ℝ) := by
    intro x y b
    show ∑ _a : α, (1 / ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))
      = 1 / (Fintype.card β : ℝ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linear_combination (1 / (Fintype.card β : ℝ)) * hn'
  have h := half_noise_mem_localSet h0 hA hB
  have e : (1 / 2 : ℝ) • uniformTable α β + (1 / 2 : ℝ) • uniformTable α β
      = uniformTable α β := by
    rw [← add_smul]
    norm_num
  rwa [e] at h

end

end CGLMPBounds
