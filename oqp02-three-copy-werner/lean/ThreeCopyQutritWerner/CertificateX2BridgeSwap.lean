module

public import ThreeCopyQutritWerner.CertificateX2BridgeS3

@[expose] public section


/-!
# Swapping the first two sites on a right-associated frame index

A three-site frame index of a type triple `(a, a, c)` lives in `Fin (m * (m * k))`
(`i = finProdFinEquiv (i₀, finProdFinEquiv (i₁, i₂))`, the row-major ambient index). Swapping the
two equal sites is the involution `x2SwapFirst m k`; its permutation matrix `x2SwapMat m k` is a
self-adjoint involution, and it commutes with every matrix invariant under the swap of both
indices, in particular with every right-associated tensor `A ⊗ (A ⊗ C)` (`x2SwapMat_comm_kron`).
With `x2InvolutionPart` (CertificateX2BridgeS3) this gives the two parts of a pair-equal type triple.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Swap of the first two sites on `Fin (m * (m * k))`. -/
def x2SwapFirstFun (m k : ℕ) (i : Fin (m * (m * k))) : Fin (m * (m * k)) :=
  finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1,
    finProdFinEquiv ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2))

theorem x2SwapFirstFun_involutive (m k : ℕ) : Function.Involutive (x2SwapFirstFun m k) := by
  intro i
  simp only [x2SwapFirstFun, Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The swap as a permutation. -/
def x2SwapFirst (m k : ℕ) : Equiv.Perm (Fin (m * (m * k))) :=
  Function.Involutive.toPerm _ (x2SwapFirstFun_involutive m k)

/-- The swap's permutation matrix. -/
def x2SwapMat (m k : ℕ) : Matrix (Fin (m * (m * k))) (Fin (m * (m * k))) ℂ :=
  Matrix.of fun i j => if x2SwapFirstFun m k i = j then 1 else 0

theorem x2SwapMat_mul_apply (m k : ℕ) (M : Matrix (Fin (m * (m * k))) (Fin (m * (m * k))) ℂ)
    (i j : Fin (m * (m * k))) :
    (x2SwapMat m k * M) i j = M (x2SwapFirstFun m k i) j := by
  simp only [x2SwapMat, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem x2SwapMat_apply_mul (m k : ℕ) (M : Matrix (Fin (m * (m * k))) (Fin (m * (m * k))) ℂ)
    (i j : Fin (m * (m * k))) :
    (M * x2SwapMat m k) i j = M i (x2SwapFirstFun m k j) := by
  simp only [x2SwapMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (x2SwapFirstFun m k j)]
  · rw [if_pos (x2SwapFirstFun_involutive m k j)]
  · intro l _ hl
    rw [if_neg]
    intro h
    apply hl
    rw [← h, x2SwapFirstFun_involutive m k l]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem x2SwapMat_mul_self (m k : ℕ) : x2SwapMat m k * x2SwapMat m k = 1 := by
  ext i j
  rw [x2SwapMat_mul_apply]
  simp only [x2SwapMat, Matrix.of_apply, Matrix.one_apply, x2SwapFirstFun_involutive m k i]

theorem x2SwapMat_conjTranspose (m k : ℕ) : (x2SwapMat m k)ᴴ = x2SwapMat m k := by
  ext i j
  simp only [x2SwapMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : x2SwapFirstFun m k j = i
  · rw [if_pos h, if_pos (by rw [← h, x2SwapFirstFun_involutive m k j]), star_one]
  · rw [if_neg h, if_neg (fun h' => h (by rw [← h', x2SwapFirstFun_involutive m k i])), star_zero]

/-- The swap commutes with every matrix invariant under swapping both indices. -/
theorem x2SwapMat_comm (m k : ℕ) (M : Matrix (Fin (m * (m * k))) (Fin (m * (m * k))) ℂ)
    (hM : ∀ i j, M (x2SwapFirstFun m k i) (x2SwapFirstFun m k j) = M i j) :
    M * x2SwapMat m k = x2SwapMat m k * M := by
  ext i j
  rw [x2SwapMat_mul_apply, x2SwapMat_apply_mul, ← hM i (x2SwapFirstFun m k j),
    x2SwapFirstFun_involutive m k j]

/-- Right-associated tensors with equal first two factors are swap invariant. -/
theorem x2SwapMat_comm_kron (m k : ℕ) (A : Matrix (Fin m) (Fin m) ℂ)
    (C : Matrix (Fin k) (Fin k) ℂ) :
    ((A ⊗ₖ (A ⊗ₖ C).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) * x2SwapMat m k =
      x2SwapMat m k * ((A ⊗ₖ (A ⊗ₖ C).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  apply x2SwapMat_comm
  intro i j
  simp only [x2SwapFirstFun, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.symm_apply_apply]
  ring

end ThreeCopyQutritWerner

end
