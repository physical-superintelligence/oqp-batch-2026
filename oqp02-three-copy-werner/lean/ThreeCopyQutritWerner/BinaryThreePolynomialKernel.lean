module

public import ThreeCopyQutritWerner.BinaryPolynomialKernel

@[expose] public section


/-!
# Original three-copy endpoint zeros and the replica polynomial

The only coordinate change here replaces the three-register tuple by its
three binary site values. The operator remains the original tripleCopy psym,
and the final theorem uses the original spin matrix and endpoint energy.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Register order is site zero, then site one, then site two. -/
def binaryThreeWordEquiv : (Fin 3 → Fin 2) ≃ (Fin 2 × Fin 2 × Fin 2) where
  toFun w := (w 0, w 1, w 2)
  invFun a := ![a.1, a.2.1, a.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv a := rfl

/-- Reindex original entries without a conjugation or a normalization. -/
def binaryThreeWordMatrix
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  K.submatrix binaryThreeWordEquiv binaryThreeWordEquiv

/-- The finite-word operator is the literal original three-copy operator. -/
theorem binaryThree_symmetrizer_entry (a b c d : Fin 3 → Fin 2) :
    binaryReplicaSymmetrizer (a, b) (c, d) =
      tripleCopy psym (binaryThreeWordEquiv a, binaryThreeWordEquiv b)
        (binaryThreeWordEquiv c, binaryThreeWordEquiv d) := by
  simp only [binaryReplicaSymmetrizer, Fin.prod_univ_three]
  rfl

/-- Original projected entries are recovered with exactly the same register order. -/
theorem binaryThree_symmetrizer_mulVec
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (a b : Fin 3 → Fin 2) :
    (binaryReplicaSymmetrizer *ᵥ vec (binaryThreeWordMatrix K)) (a, b) =
      (tripleCopy psym *ᵥ vec K) (binaryThreeWordEquiv a, binaryThreeWordEquiv b) := by
  simp only [Matrix.mulVec, dotProduct]
  apply Fintype.sum_equiv (binaryThreeWordEquiv.prodCongr binaryThreeWordEquiv)
  intro p
  rw [binaryThree_symmetrizer_entry]
  rfl

/-- Exact physical symmetric kernel, with every original matrix entry retained. -/
theorem binaryThree_symmetric_kernel_iff_polynomial_zero
    (K : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    tripleCopy psym *ᵥ vec K = 0 ↔
      binaryReplicaPolynomial (binaryThreeWordMatrix K) = 0 := by
  rw [← binaryReplicaSymmetrizer_kernel_iff]
  constructor
  · intro h
    funext p
    rw [binaryThree_symmetrizer_mulVec, h]
    rfl
  · intro h
    funext p
    have he := congrFun h
      (binaryThreeWordEquiv.symm p.1, binaryThreeWordEquiv.symm p.2)
    simpa only [binaryThree_symmetrizer_mulVec, Equiv.apply_symm_apply,
      Pi.zero_apply] using he

/-- The original binary endpoint zero is exactly the replica polynomial
equation after the actual spin transform, without a rank premise. -/
theorem binary_endpoint_zero_iff_replica_polynomial_zero
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ) :
    endpointEnergy C = 0 ↔
      binaryReplicaPolynomial (binaryThreeWordMatrix (C * epsJ₃ᵀ)) = 0 := by
  rw [binary_endpoint_zero_iff_symmetric_kernel,
    binaryThree_symmetric_kernel_iff_polynomial_zero]

end ThreeCopyQutritWerner
