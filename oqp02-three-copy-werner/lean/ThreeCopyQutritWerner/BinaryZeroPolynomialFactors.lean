module

public import ThreeCopyQutritWerner.BinaryThreePolynomialKernel
public import ThreeCopyQutritWerner.RankTwoReplicaRays
public import ThreeCopyQutritWerner.RankOne

@[expose] public section


/-!
# Separated polynomial factors of actual binary endpoint zeros

The rank-two decomposition and polynomial equation are derived from the
original nonzero endpoint zero. Neither is an additional premise. The final
site-partition tensor assembly and normalization into the manuscript families
remain separate obligations.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- The original invertible spin transform retains the exact matrix rank. -/
theorem binaryThree_spin_word_rank
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    (binaryThreeWordMatrix (C * epsJ₃ᵀ)).rank = C.rank := by
  rw [binaryThreeWordMatrix, Matrix.rank_submatrix]
  apply le_antisymm
  · exact Matrix.rank_mul_le_left _ _
  · calc
      C.rank = (C * epsJ₃ᵀ * epsJ₃).rank := by
        rw [Matrix.mul_assoc, epsJ₃_transpose_mul_self, Matrix.mul_one]
      _ ≤ (C * epsJ₃ᵀ).rank := Matrix.rank_mul_le_left _ _

/-- Every original nonzero binary endpoint zero of rank at most two has
actual nonzero replica rays whose tensor polynomials admit a separated grid. -/
theorem binary_endpoint_zero_exists_separated_polynomial_factors
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hC : C.rank ≤ 2) (hz : endpointEnergy C = 0) (hne : C ≠ 0) :
    ∃ x y z t : (Fin 3 → Fin 2) → ℂ, ∃ p q r s : MvPolynomial (Fin 3) ℂ,
      x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ t ≠ 0 ∧
      binaryThreeWordMatrix (C * epsJ₃ᵀ) = (fun a b => x a * y b - z a * t b) ∧
      p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0 ∧
      binaryTensorPolynomial x = p * r ∧ binaryTensorPolynomial y = q * s ∧
      binaryTensorPolynomial z = p * s ∧ binaryTensorPolynomial t = q * r ∧
      (∀ i, (p.degreeOf i = 0 ∧ q.degreeOf i = 0) ∨
        (r.degreeOf i = 0 ∧ s.degreeOf i = 0)) := by
  have hr : (binaryThreeWordMatrix (C * epsJ₃ᵀ)).rank = 2 := by
    rw [binaryThree_spin_word_rank]
    exact rank_eq_two_of_endpointEnergy_eq_zero C hC hz hne
  obtain ⟨x, z, y, t, hx, hy, hzz, ht, hrep⟩ :=
    rank_two_exists_replica_ray_difference _ hr
  have hp := (binary_endpoint_zero_iff_replica_polynomial_zero C).mp hz
  rw [hrep] at hp
  obtain ⟨p, q, r, s, hrest⟩ :=
    binaryReplicaPolynomial_zero_separated_factors x y z t hx hy hzz hp
  exact ⟨x, y, z, t, p, q, r, s, hx, hy, hzz, ht, hrep, hrest⟩

end ThreeCopyQutritWerner
