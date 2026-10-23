module

public import ThreeCopyQutritWerner.TwoQubitPPTSufficiency

@[expose] public section


/-! Necessity in arbitrary finite bipartite dimensions, and the exact
positive-partial-transpose equivalence for two qubits. -/
noncomputable section
open scoped BigOperators Matrix Kronecker MatrixOrder ComplexOrder
namespace ThreeCopyQutritWerner

theorem IsBipartiteSeparable.posSemidef {m n : Type*} [Fintype m] [Fintype n]
    {ρ : Matrix (m × n) (m × n) ℂ} (hρ : IsBipartiteSeparable ρ) : ρ.PosSemidef := by
  classical
  obtain ⟨K, p, A, B, hp, hA, hB, rfl⟩ := hρ
  apply Matrix.posSemidef_sum
  intro k _
  apply ((hA k).kronecker (hB k)).smul
  exact Complex.nonneg_iff.mpr ⟨hp k, by simp⟩

theorem IsBipartiteSeparable.partialTranspose_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    {ρ : Matrix (m × n) (m × n) ℂ} (hρ : IsBipartiteSeparable ρ) :
    (partialTranspose ρ).PosSemidef := by
  classical
  obtain ⟨K, p, A, B, hp, hA, hB, rfl⟩ := hρ
  have he : partialTranspose (∑ k, (p k : ℂ) • (A k ⊗ₖ B k)) =
      ∑ k, (p k : ℂ) • (A k ⊗ₖ (B k)ᵀ) := by
    ext i j
    simp [partialTranspose, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  rw [he]
  apply Matrix.posSemidef_sum
  intro k _
  apply ((hA k).kronecker (hB k).transpose).smul
  exact Complex.nonneg_iff.mpr ⟨hp k, by simp⟩

/-- The two-qubit criterion uses the original finite-product predicate,
and includes both positivity conditions without a trace-one restriction. -/
theorem twoQubit_separable_iff_ppt
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    IsBipartiteSeparable ρ ↔ ρ.PosSemidef ∧ (partialTranspose ρ).PosSemidef :=
  ⟨fun h => ⟨h.posSemidef, h.partialTranspose_posSemidef⟩,
    fun h => twoQubit_ppt_separable ρ h.1 h.2⟩

end ThreeCopyQutritWerner
