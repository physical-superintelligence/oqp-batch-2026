module

public import CGLMPBounds.Partition.ConsecutiveBasics

@[expose] public section


/-! Exact finite interval decomposition of the literal D.2 Fourier
coefficients. The endpoints may repeat; interval additivity automatically
gives zero contribution from empty cells. -/

namespace CGLMPBounds.Partition
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section

lemma ConsecutivePartition.sum_cell_integrals {d : ℕ} (ℓ : ConsecutivePartition d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : ∀ j : Fin d,
      IntervalIntegrable f volume (ℓ.boundary j.castSucc) (ℓ.boundary j.succ)) :
    (∑ j : Fin d, ∫ t in (ℓ.boundary j.castSucc)..(ℓ.boundary j.succ), f t) =
      ∫ t in (0 : ℝ)..1, f t := by
  let b : ℕ → ℝ := fun n => ℓ.boundary ⟨min n d, Nat.lt_succ_iff.mpr (Nat.min_le_right n d)⟩
  have hb₀ : b 0 = 0 := by simpa [b] using ℓ.boundary_zero
  have hbd : b d = 1 := by simpa [b, Fin.last] using ℓ.boundary_one
  have hbj (j : Fin d) : b j.val = ℓ.boundary j.castSucc := by
    simp only [b, Nat.min_eq_left j.isLt.le]
    rfl
  have hbjs (j : Fin d) : b (j.val + 1) = ℓ.boundary j.succ := by
    simp only [b, Nat.min_eq_left (Nat.succ_le_of_lt j.isLt)]
    rfl
  have hi (k : ℕ) (hk : k < d) : IntervalIntegrable f volume (b k) (b (k + 1)) := by
    simpa only [hbj ⟨k, hk⟩, hbjs ⟨k, hk⟩] using hf ⟨k, hk⟩
  have he := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [Finset.sum_range, hb₀, hbd] at he
  simpa only [hbj, hbjs] using he

private lemma consecutive_fourier_integrand_on_cell {d r : ℕ}
    (ℓ : ConsecutivePartition d) (V : Fin d → Circulation.Mat r)
    (n : ℕ) (j : Fin d) {t : ℝ} (ht : t ∈ ℓ.cell j) :
    Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) •
      consecutivePartitionBranch ℓ V t =
      Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * t : ℝ) : ℂ)) * Complex.I) •
        (V j)ᴴ := by
  rw [consecutivePartitionBranch, consecutivePartitionStep_eq ℓ V j ht, smul_smul,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The actual negative Fourier coefficient is the finite sum of the
cell exponential integrals times the actual dagger labels. -/
theorem consecutivePartitionBranch_negative_coefficient {d r : ℕ}
    (ℓ : ConsecutivePartition d) (V : Fin d → Circulation.Mat r) (n : ℕ) :
    matrixNegativeFourierCoefficient (consecutivePartitionBranch ℓ V) n =
      ∑ j : Fin d,
        (∫ t in (ℓ.boundary j.castSucc)..(ℓ.boundary j.succ),
          Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * t : ℝ) : ℂ)) * Complex.I)) •
          (V j)ᴴ := by
  letI : ENormedAddMonoid (Circulation.Mat r) :=
    inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))
  let F : ℝ → Circulation.Mat r := fun t =>
    Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) •
      consecutivePartitionBranch ℓ V t
  let G : ℝ → ℂ := fun t =>
    Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * t : ℝ) : ℂ)) * Complex.I)
  have hb (j : Fin d) : ℓ.boundary j.castSucc ≤ ℓ.boundary j.succ :=
    ℓ.monotone_boundary (by exact_mod_cast (show j.val ≤ j.val + 1 by omega))
  have he (j : Fin d) : EqOn (fun t => G t • (V j)ᴴ) F
      (uIoo (ℓ.boundary j.castSucc) (ℓ.boundary j.succ)) := by
    rw [uIoo_of_le (hb j)]
    intro t ht
    exact (consecutive_fourier_integrand_on_cell ℓ V n j ⟨ht.1.le, ht.2⟩).symm
  have hi (j : Fin d) :
      IntervalIntegrable F volume (ℓ.boundary j.castSucc) (ℓ.boundary j.succ) := by
    have hc : Continuous (fun t => G t • (V j)ᴴ) := by
      dsimp [G]
      fun_prop
    exact (hc.intervalIntegrable (ℓ.boundary j.castSucc)
      (ℓ.boundary j.succ)).congr_uIoo (he j)
  change (∫ t in (0 : ℝ)..1, F t) = _
  rw [← ℓ.sum_cell_integrals F hi]
  apply Finset.sum_congr rfl
  intro j _
  rw [← intervalIntegral.integral_congr_uIoo (he j), intervalIntegral.integral_smul_const]

theorem consecutivePartition_scalar_coefficients_sum {d : ℕ}
    (ℓ : ConsecutivePartition d) (n : ℕ) :
    (∑ j : Fin d,
      ∫ t in (ℓ.boundary j.castSucc)..(ℓ.boundary j.succ),
        Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * t : ℝ) : ℂ)) * Complex.I)) =
      ∫ t in (0 : ℝ)..1,
        Complex.exp ((((Real.pi / 2 * (4 * (n : ℝ) + 3) * t : ℝ) : ℂ)) * Complex.I) := by
  apply ℓ.sum_cell_integrals
  intro j
  exact (by fun_prop : Continuous _).intervalIntegrable
    (ℓ.boundary j.castSucc) (ℓ.boundary j.succ)

end
end CGLMPBounds.Partition
