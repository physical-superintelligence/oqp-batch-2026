module

public import CGLMPBounds.Defs.TensorCHSHStatistics
public import CGLMPBounds.TensorCHSH.Binomial
public import CGLMPBounds.TensorCHSH.Visibility

@[expose] public section


/-!
# Witness values of the tensor CHSH table as binomial tails

Proof of Theorem A.3 (Appendix F.2): under `T_M` each error count is `Bin(M, r)` and under uniform
noise it is `Bin(M, 1/2)`, so `G_{M,k}` equals the difference of a lower and an upper binomial
tail. Stated for the closed-formula table `tensorTable m ρ` of (F.5).
-/

namespace CGLMPBounds.TensorCHSH

noncomputable section

theorem bell_witnessTable_tensorTable (m k h : ℕ) (ρ : ℝ) :
    bell (witnessTable m k h) (tensorTable m ρ) = 4 * tailDiff m k h ρ := by
  rw [bell_apply]
  have hxy : ∀ x y : Fin 2,
      ∑ a, ∑ b, witnessTable m k h x y a b * tensorTable m ρ x y a b = tailDiff m k h ρ := by
    intro x y
    exact sum_sum_tensorTable ρ
      (fun j => (if j ≤ k then (1 : ℝ) else 0) - (if h ≤ j then (1 : ℝ) else 0)) x y
  simp only [hxy, Fin.sum_univ_two]
  ring

theorem bell_witnessTable_uniformTable (m k h : ℕ) :
    bell (witnessTable m k h) (uniformTable (Fin m → Bool) (Fin m → Bool))
      = 4 * tailDiff m k h (1 / 2) := by
  rw [← tensorTable_half]
  exact bell_witnessTable_tensorTable m k h (1 / 2)

/-- If `G_{m,k}(v₀ T + (1 - v₀) u) > 1/2` in terms of binomial tails, then `v_crit < v₀`. -/
theorem critVisibility_tensorTable_lt {m k : ℕ} (hk : 4 * k < m) {ρ v₀ : ℝ} (hv₀ : 0 < v₀)
    (h : 1 / 2 < v₀ * tailDiff m k (m - 3 * k) ρ
      + (1 - v₀) * tailDiff m k (m - 3 * k) (1 / 2)) :
    critVisibility (tensorTable m ρ) < v₀ := by
  refine critVisibility_lt_of_witnessTable hk hv₀ ?_
  rw [bell_witnessTable_tensorTable, bell_witnessTable_uniformTable]
  nlinarith [h]

end

end CGLMPBounds.TensorCHSH
