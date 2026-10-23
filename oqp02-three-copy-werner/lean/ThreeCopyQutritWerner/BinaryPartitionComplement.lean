module

public import ThreeCopyQutritWerner.BinaryPartitionHalfNorm
public import ThreeCopyQutritWerner.BinaryPartitionSpin
public import ThreeCopyQutritWerner.ZeroRelations

@[expose] public section


/-!
# A singleton skew side gives the normalized identity tensor family

The one-qubit skew matrix is a scalar epsilon. Undoing spin makes it a
scalar identity, and the remaining rank-one factor has exactly half unit
Frobenius norm. Its entire phase is absorbed into a unit vector.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

theorem binaryPartition_complement_spin_factors
    (D : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (p q : (Fin 2 × Fin 2) → ℂ) (r s : Fin 2 → ℂ)
    (he : D * epsJ₃ᵀ = (fun a b => r a * s b - s a * r b) ⊗ₖ
      (fun a b => p a * q b)) :
    ∃ T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      T.rank ≤ 1 ∧ D = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T := by
  let S : Matrix (Fin 2) (Fin 2) ℂ := fun a b => r a * s b - s a * r b
  let A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun a b => p a * q b
  have hS : S = S 0 1 • epsMat := by
    apply skew_fin_two_eq_smul_eps
    ext a b
    change r b * s a - s b * r a = -(r a * s b - s a * r b)
    ring
  let T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := (-S 0 1) • (A * epsJ₂)
  have hT : T =
      (show Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ from
        fun a b => ((-S 0 1) * p a) * q b) * epsJ₂ := by
    dsimp [T]
    rw [← Matrix.smul_mul]
    congr 1
    ext a b
    change (-S 0 1) * (p a * q b) = ((-S 0 1) * p a) * q b
    ring
  have hSE : S * epsMat = (-S 0 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    conv_lhs => rw [hS, Matrix.smul_mul, epsMat_mul_self]
    ext a b
    simp [Matrix.smul_apply, smul_eq_mul]
  refine ⟨T, ?_, ?_⟩
  · rw [hT]
    exact (Matrix.rank_mul_le_left _ _).trans
      (Matrix.rank_vecMulVec_le (fun a => (-S 0 1) * p a) q)
  · calc
      D = (D * epsJ₃ᵀ) * epsJ₃ := by
        rw [Matrix.mul_assoc, epsJ₃_transpose_mul_self, Matrix.mul_one]
      _ = (S ⊗ₖ A) * (epsMat ⊗ₖ epsJ₂) := by rw [he]; rfl
      _ = (S * epsMat) ⊗ₖ (A * epsJ₂) := (Matrix.mul_kronecker_mul _ _ _ _).symm
      _ = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ T := by
        rw [hSE]
        ext a b
        simp only [T, Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
        ring

/-- The original normalized matrix in the complementary-singleton branch
has exactly the manuscript's 1/sqrt(2) identity coefficient and unit vectors. -/
theorem binaryPartition_complement_normalized_identity
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hN : frobSq C = 1) (i : Fin 3)
    (p q : (↥(({i} : Finset (Fin 3))ᶜ) → Fin 2) → ℂ)
    (r s : (↥((({i} : Finset (Fin 3))ᶜ)ᶜ) → Fin 2) → ℂ)
    (he : binaryThreeWordMatrix (C * epsJ₃ᵀ) = binaryPartitionMatrix {i}ᶜ p q r s) :
    ∃ x y : (Fin 2 × Fin 2) → ℂ, vecNormSq x = 1 ∧ vecNormSq y = 1 ∧
      C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) =
        ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ ketBra x y := by
  obtain ⟨p', q', r', s', hparts⟩ :=
    binaryPartition_complement_singleton_kronecker i p q r s
  have hspin : C.submatrix (binaryPartitionSiteTuple i) (binaryPartitionSiteTuple i) *
      epsJ₃ᵀ = (fun a b => r' a * s' b - s' a * r' b) ⊗ₖ
        (fun a b => p' a * q' b) := by
    rw [← binaryPartitionSiteWord_spin_original, he]
    exact hparts
  obtain ⟨T, hT, hD⟩ := binaryPartition_complement_spin_factors _ p' q' r' s' hspin
  have hF := (binaryPartitionSiteTuple_rank_frob C i).2.trans hN
  have hI : frobSq (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
    norm_num [frobSq, Matrix.one_apply, Fin.sum_univ_two]
  rw [hD, ← tensor₂_eq_kronecker, frobSq_tensor₂, hI] at hF
  obtain ⟨x, y, hx, hy, hxy⟩ := binaryPartition_rank_one_half_norm T hT (by linarith)
  refine ⟨x, y, hx, hy, hD.trans ?_⟩
  rw [hxy]
  ext a b
  simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end ThreeCopyQutritWerner
