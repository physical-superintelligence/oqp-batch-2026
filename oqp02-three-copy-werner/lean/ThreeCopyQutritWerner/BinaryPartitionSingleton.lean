module

public import ThreeCopyQutritWerner.BinaryPartitionNormalize
public import ThreeCopyQutritWerner.BinaryPartitionSpin

@[expose] public section


/-!
# The singleton first partition is the normalized B₂ tensor family

Undoing the original spin sends the one-site rank-one factor to another
actual rank-one factor, and the remaining skew factor to an operator with
skew two-site spin. Normalization is then derived from the original C.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem binaryPartition_epsJ₂_transpose_eq_self : epsJ₂ᵀ = epsJ₂ := by
  rw [epsJ₂_transpose, epsMat_transpose]
  ext a b
  simp [epsJ₂, Matrix.kroneckerMap_apply]

theorem binaryPartition_singleton_spin_factors
    (D : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (p q : Fin 2 → ℂ) (r s : (Fin 2 × Fin 2) → ℂ)
    (he : D * epsJ₃ᵀ = (fun a b => p a * q b) ⊗ₖ
      (fun a b => r a * s b - s a * r b)) :
    ∃ u v : Fin 2 → ℂ, ∃ T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      D = ketBra u v ⊗ₖ T ∧ (T * epsJ₂)ᵀ = -(T * epsJ₂) := by
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    (show Matrix (Fin 2) (Fin 2) ℂ from fun a b => p a * q b) * epsMat
  let S : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    fun a b => r a * s b - s a * r b
  have hA : A.rank ≤ 1 :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_vecMulVec_le p q)
  obtain ⟨u, v, huv⟩ := exists_eq_ketBra_of_rank_le_one A hA
  have hD : D = A ⊗ₖ (S * epsJ₂) := by
    calc
      D = (D * epsJ₃ᵀ) * epsJ₃ := by
        rw [Matrix.mul_assoc, epsJ₃_transpose_mul_self, Matrix.mul_one]
      _ = ((fun a b => p a * q b) ⊗ₖ S) * (epsMat ⊗ₖ epsJ₂) := by rw [he]; rfl
      _ = A ⊗ₖ (S * epsJ₂) := (Matrix.mul_kronecker_mul _ _ _ _).symm
  have hJJ : epsJ₂ * epsJ₂ = 1 := by
    rw [← binaryPartition_epsJ₂_transpose_eq_self]
    exact epsJ₂_transpose_mul_transpose
  refine ⟨u, v, S * epsJ₂, ?_, ?_⟩
  · simpa only [huv] using hD
  · rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
    ext a b
    change r b * s a - s b * r a = -(r a * s b - s a * r b)
    ring

/-- A singleton tensor partition of the actual original normalized matrix
is exactly family II in one of the three literal site placements. -/
theorem binaryPartition_singleton_normalized_binaryB₂
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank = 2) (hN : frobSq C = 1) (i : Fin 3)
    (p q : (({i} : Finset (Fin 3)) → Fin 2) → ℂ)
    (r s : (↥(({i} : Finset (Fin 3))ᶜ) → Fin 2) → ℂ)
    (he : binaryThreeWordMatrix (C * epsJ₃ᵀ) = binaryPartitionMatrix {i} p q r s) :
    ∃ x y : Fin 2 → ℂ, ∃ U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ,
      vecNormSq x = 1 ∧ vecNormSq y = 1 ∧ Uᴴ * U = 1 ∧
        C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) =
          ketBra x y ⊗ₖ binaryB₂ U := by
  obtain ⟨p', q', r', s', hparts⟩ := binaryPartition_singleton_kronecker i p q r s
  have hspin : C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) *
      epsJ₃ᵀ = (fun a b => p' a * q' b) ⊗ₖ
        (fun a b => r' a * s' b - s' a * r' b) := by
    rw [← binaryPartitionSiteWord_spin_original, he]
    exact hparts
  obtain ⟨u, v, T, hD, hskew⟩ := binaryPartition_singleton_spin_factors _ p' q' r' s' hspin
  obtain ⟨hR, hF⟩ := binaryPartitionSiteTuple_rank_frob C i
  rw [hD, hC] at hR
  rw [hD, hN] at hF
  obtain ⟨x, y, U, hx, hy, hU, hnormal⟩ :=
    binaryPartition_normalized_skew_tensor_binaryB₂ u v T hR hF hskew
  exact ⟨x, y, U, hx, hy, hU, hD.trans hnormal⟩

end ThreeCopyQutritWerner
