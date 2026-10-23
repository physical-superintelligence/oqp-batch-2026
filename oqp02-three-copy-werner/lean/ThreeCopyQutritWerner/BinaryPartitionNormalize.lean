module

public import ThreeCopyQutritWerner.BinaryPartitionRank
public import ThreeCopyQutritWerner.SkewNormalizedFrame
public import ThreeCopyQutritWerner.TwoPlane

@[expose] public section


/-!
# Normalizing the rank-one side of an actual binary partition

Normalize the two original vectors and absorb both their scale and complex
phase into the other matrix. Its Frobenius norm and rank are then forced by
those of the full matrix, yielding the exact B₂ family when its spin is skew.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace ThreeCopyQutritWerner

theorem binaryPartition_normalize_ketBra_tensor
    {a b : Type*} [Fintype a] [Fintype b]
    (u v : a → ℂ) (T : Matrix b b ℂ)
    (hN : frobSq (ketBra u v ⊗ₖ T) = 1) :
    ∃ x y : a → ℂ, ∃ z : ℂ, vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      ketBra u v ⊗ₖ T = ketBra x y ⊗ₖ (z • T) ∧ frobSq (z • T) = 1 := by
  have hu : ∃ i, u i ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp [frobSq, ketBra, Matrix.kroneckerMap_apply, hn] at hN
  have hv : ∃ i, v i ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp [frobSq, ketBra, Matrix.kroneckerMap_apply, hn] at hN
  obtain ⟨x, α, hx, hux⟩ := TwoPlane.exists_unit_factor u hu
  obtain ⟨y, β, hy, hvy⟩ := TwoPlane.exists_unit_factor v hv
  let z : ℂ := α * conj β
  have he : ketBra u v ⊗ₖ T = ketBra x y ⊗ₖ (z • T) := by
    ext i j
    simp only [Matrix.kroneckerMap_apply, ketBra, hux, hvy, map_mul,
      Matrix.smul_apply, smul_eq_mul]
    dsimp [z]
    ring
  refine ⟨x, y, z, hx, hy, he, ?_⟩
  rw [he, ← tensor₂_eq_kronecker, frobSq_tensor₂,
    frobSq_ketBra_vecNormSq, hx, hy, one_mul, one_mul] at hN
  exact hN

/-- Unit norm and rank two of the original product give unit local vectors
and the manuscript's literal normalized B₂ operator, without an extra phase. -/
theorem binaryPartition_normalized_skew_tensor_binaryB₂
    (u v : Fin 2 → ℂ) (T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hR : (ketBra u v ⊗ₖ T).rank = 2)
    (hN : frobSq (ketBra u v ⊗ₖ T) = 1)
    (hskew : (T * epsJ₂)ᵀ = -(T * epsJ₂)) :
    ∃ x y : Fin 2 → ℂ, ∃ U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ,
      vecNormSq x = 1 ∧ vecNormSq y = 1 ∧ Uᴴ * U = 1 ∧
        ketBra u v ⊗ₖ T = ketBra x y ⊗ₖ binaryB₂ U := by
  obtain ⟨x, y, z, hx, hy, he, hT⟩ := binaryPartition_normalize_ketBra_tensor u v T hN
  have hxne : x ≠ 0 := by
    intro h
    simp [h, vecNormSq] at hx
  have hyne : (fun j => conj (y j)) ≠ (0 : Fin 2 → ℂ) := by
    intro h
    have hzero : y = 0 := by
      funext j
      have hj := congrArg conj (congrFun h j)
      simpa using hj
    simp [hzero, vecNormSq] at hy
  have hr : (z • T).rank = 2 := by
    calc
      (z • T).rank = (ketBra x y ⊗ₖ (z • T)).rank :=
        (binaryPartition_rank_one_kronecker_rank x (fun j => conj (y j)) hxne hyne
          (z • T)).symm
      _ = (ketBra u v ⊗ₖ T).rank := congrArg Matrix.rank he.symm
      _ = 2 := hR
  have hs : ((z • T) * epsJ₂)ᵀ = -((z • T) * epsJ₂) := by
    rw [Matrix.smul_mul, Matrix.transpose_smul, hskew, smul_neg]
  obtain ⟨U, hU, hB⟩ := exists_binaryB₂_of_skew_spin (z • T) hr hT hs
  exact ⟨x, y, U, hx, hy, hU, he.trans (congrArg (fun M => ketBra x y ⊗ₖ M) hB)⟩

end ThreeCopyQutritWerner
