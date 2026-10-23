module

public import ThreeCopyQutritWerner.CoherentPencilSupport
public import ThreeCopyQutritWerner.InteriorConverse
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Normalizing actual endpoint zeros without changing physical support

The scalar is constructed from the actual Frobenius norm. Rank and all local
range dimensions are preserved. This removes the normalization restriction
from the explicitly assumed thin-source conclusion, without proving it.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- Every nonzero finite complex matrix has a nonzero scalar normalization. -/
theorem exists_frobSq_normalizing_scalar {m n : Type*} [Fintype m] [Fintype n]
    (C : Matrix m n ℂ) (hC : C ≠ 0) :
    ∃ z : ℂ, z ≠ 0 ∧ frobSq (z • C) = 1 := by
  have hpos : 0 < frobSq C := by
    have hn := frobSq_nonneg C
    by_contra h
    exact hC (matrix_eq_zero_of_frobSq_eq_zero C (le_antisymm (not_lt.mp h) hn))
  have hs : Real.sqrt (frobSq C) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  refine ⟨((Real.sqrt (frobSq C))⁻¹ : ℝ), ?_, ?_⟩
  · exact_mod_cast inv_ne_zero hs
  · rw [frobSq_smul, Complex.normSq_ofReal]
    have hsq : Real.sqrt (frobSq C) * Real.sqrt (frobSq C) = frobSq C := by
      simpa only [pow_two] using Real.sq_sqrt hpos.le
    rw [← mul_inv, hsq]
    exact inv_mul_cancel₀ (ne_of_gt hpos)

/-- Nonzero scalar normalization preserves all actual local support dimensions. -/
theorem localRangeDims_smul {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (z : ℂ) (hz : z ≠ 0) :
    localRangeDim₁ (z • C) = localRangeDim₁ C ∧
      localRangeDim₂ (z • C) = localRangeDim₂ C ∧
      localRangeDim₃ (z • C) = localRangeDim₃ C := by
  have hf1 : coherentFlatten₁ (z • C) = z • coherentFlatten₁ C := rfl
  have hf2 : coherentFlatten₂ (z • C) = z • coherentFlatten₂ C := rfl
  have hf3 : coherentFlatten₃ (z • C) = z • coherentFlatten₃ C := rfl
  simp only [localRangeDim₁_eq_coherentFlatten_rank, localRangeDim₂_eq_coherentFlatten_rank,
    localRangeDim₃_eq_coherentFlatten_rank, hf1, hf2, hf3,
    Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hz),
    and_self]

/-- REDUCTION: the normalized thin-source property applies to every nonzero
actual rank-at-most-two endpoint zero after faithful scalar normalization. -/
theorem hasThinLocalRange_of_thinSourceProperty (hthin : ThinSourceProperty)
    (C : Matrix QutritSites QutritSites ℂ) (hr : C.rank ≤ 2)
    (hC : C ≠ 0) (hq : endpointEnergy C = 0) : HasThinLocalRange C := by
  obtain ⟨z, hz, hN⟩ := exists_frobSq_normalizing_scalar C hC
  have hrz : (z • C).rank ≤ 2 := by
    rwa [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hz)]
  have hqz : endpointEnergy (z • C) = 0 := by
    rw [endpointEnergy, energy_smul]
    change Complex.normSq z * endpointEnergy C = 0
    rw [hq, mul_zero]
  have ht := hthin (z • C) hrz hN hqz
  obtain ⟨h1, h2, h3⟩ := localRangeDims_smul C z hz
  simpa only [HasThinLocalRange, h1, h2, h3] using ht

end ThreeCopyQutritWerner
