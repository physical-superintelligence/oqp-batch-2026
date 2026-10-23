module

public import ThreeCopyQutritWerner.CertificateX2BridgeSwap

@[expose] public section


/-!
# Swapping the last two sites on a right-associated frame index

The mirror of CertificateX2BridgeSwap for type triples `(a, c, c)`: on `Fin (k * (m * m))` the
swap of the last two sites is a self-adjoint involution commuting with swap-invariant matrices,
in particular with right-associated tensors `A ⊗ (C ⊗ C)`.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Swap of the last two sites on `Fin (k * (m * m))`. -/
def x2SwapLastFun (k m : ℕ) (i : Fin (k * (m * m))) : Fin (k * (m * m)) :=
  finProdFinEquiv ((finProdFinEquiv.symm i).1,
    finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm i).2).2,
      (finProdFinEquiv.symm (finProdFinEquiv.symm i).2).1))

theorem x2SwapLastFun_involutive (k m : ℕ) : Function.Involutive (x2SwapLastFun k m) := by
  intro i
  simp only [x2SwapLastFun, Equiv.symm_apply_apply, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The swap's permutation matrix. -/
def x2SwapLastMat (k m : ℕ) : Matrix (Fin (k * (m * m))) (Fin (k * (m * m))) ℂ :=
  Matrix.of fun i j => if x2SwapLastFun k m i = j then 1 else 0

theorem x2SwapLastMat_mul_apply (k m : ℕ) (M : Matrix (Fin (k * (m * m))) (Fin (k * (m * m))) ℂ)
    (i j : Fin (k * (m * m))) :
    (x2SwapLastMat k m * M) i j = M (x2SwapLastFun k m i) j := by
  simp only [x2SwapLastMat, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem x2SwapLastMat_apply_mul (k m : ℕ) (M : Matrix (Fin (k * (m * m))) (Fin (k * (m * m))) ℂ)
    (i j : Fin (k * (m * m))) :
    (M * x2SwapLastMat k m) i j = M i (x2SwapLastFun k m j) := by
  simp only [x2SwapLastMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (x2SwapLastFun k m j)]
  · rw [if_pos (x2SwapLastFun_involutive k m j)]
  · intro l _ hl
    rw [if_neg]
    intro h
    apply hl
    rw [← h, x2SwapLastFun_involutive k m l]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem x2SwapLastMat_mul_self (k m : ℕ) : x2SwapLastMat k m * x2SwapLastMat k m = 1 := by
  ext i j
  rw [x2SwapLastMat_mul_apply]
  simp only [x2SwapLastMat, Matrix.of_apply, Matrix.one_apply, x2SwapLastFun_involutive k m i]

theorem x2SwapLastMat_conjTranspose (k m : ℕ) : (x2SwapLastMat k m)ᴴ = x2SwapLastMat k m := by
  ext i j
  simp only [x2SwapLastMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : x2SwapLastFun k m j = i
  · rw [if_pos h, if_pos (by rw [← h, x2SwapLastFun_involutive k m j]), star_one]
  · rw [if_neg h, if_neg (fun h' => h (by rw [← h', x2SwapLastFun_involutive k m i])), star_zero]

theorem x2SwapLastMat_comm (k m : ℕ) (M : Matrix (Fin (k * (m * m))) (Fin (k * (m * m))) ℂ)
    (hM : ∀ i j, M (x2SwapLastFun k m i) (x2SwapLastFun k m j) = M i j) :
    M * x2SwapLastMat k m = x2SwapLastMat k m * M := by
  ext i j
  rw [x2SwapLastMat_mul_apply, x2SwapLastMat_apply_mul, ← hM i (x2SwapLastFun k m j),
    x2SwapLastFun_involutive k m j]

theorem x2SwapLastMat_comm_kron (k m : ℕ) (A : Matrix (Fin k) (Fin k) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) :
    ((A ⊗ₖ (C ⊗ₖ C).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) * x2SwapLastMat k m =
      x2SwapLastMat k m * ((A ⊗ₖ (C ⊗ₖ C).submatrix finProdFinEquiv.symm finProdFinEquiv.symm).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  apply x2SwapLastMat_comm
  intro i j
  simp only [x2SwapLastFun, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.symm_apply_apply]
  ring

end ThreeCopyQutritWerner

end
