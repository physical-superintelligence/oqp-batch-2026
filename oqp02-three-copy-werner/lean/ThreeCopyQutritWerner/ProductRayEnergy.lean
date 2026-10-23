module

public import ThreeCopyQutritWerner.ProductRayPolarization
public import ThreeCopyQutritWerner.ProductRayLocal
public import ThreeCopyQutritWerner.BinaryZeros

@[expose] public section


/-!
# Canonical product-ray completed-square identity

The matrix is literally `C(i,j)=1_{i=000} b(j)+x(i)d(j)`, with arbitrary
complex covectors `b,d`. Its energy is the repository's unnormalized-trace
`endpointEnergy`. The residual acts on `x ⊗ conj(d)`, with the three physical
sites regrouped. No rank, normalization or endpoint-sign premise is imposed.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace ThreeCopyQutritWerner

abbrev ProductRayShore := Fin 3 × Fin 3 × Fin 3
abbrev ProductRayThreePairs := ProductRayPair × ProductRayPair × ProductRayPair

/-- Rectangular tensor cube, with the same right-associated coordinates as `tensor₃`. -/
def productRayRectCube {m n : Type*} (M : Matrix m n ℂ) :
    Matrix (m × m × m) (n × n × n) ℂ :=
  fun i j => M i.1 j.1 * M i.2.1 j.2.1 * M i.2.2 j.2.2

theorem productRayRectCube_eq_kronecker {m n : Type*} (M : Matrix m n ℂ) :
    productRayRectCube M = M ⊗ₖ (M ⊗ₖ M) := by
  ext i j
  simp only [productRayRectCube, Matrix.kroneckerMap_apply, mul_assoc]

theorem productRayRectCube_mul {l m n : Type*} [Fintype m]
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    productRayRectCube (A * B) = productRayRectCube A * productRayRectCube B := by
  simp only [productRayRectCube_eq_kronecker, Matrix.mul_kronecker_mul]

theorem productRayRectCube_conjTranspose {m n : Type*} (A : Matrix m n ℂ) :
    productRayRectCube Aᴴ = (productRayRectCube A)ᴴ := by
  ext i j
  simp only [productRayRectCube, Matrix.conjTranspose_apply, star_mul']

theorem productRayRectCube_one {n : Type*} [DecidableEq n] :
    productRayRectCube (1 : Matrix n n ℂ) = 1 := by
  simp only [productRayRectCube_eq_kronecker, Matrix.one_kronecker_one]

theorem productRayRectCube_hermitian {n : Type*} (M : Matrix n n ℂ) (hM : Mᴴ = M) :
    (productRayRectCube M)ᴴ = productRayRectCube M := by
  rw [← productRayRectCube_conjTranspose, hM]

/-- The canonical-ray embedding at one site. -/
def productRayE : Matrix ProductRayPair (Fin 3) ℂ :=
  fun ij k => if ij.1 = 0 ∧ ij.2 = k then 1 else 0

/-- Positive local coefficient of the canonical-ray summand. -/
def productRayD : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1 / 2, 1, 1]

set_option maxHeartbeats 2000000 in
theorem productRayE_adjoint_T :
    productRayEᴴ * partialTranspose productRayA = productRayL := by
  ext i ⟨j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [productRayE, productRayA, productRayL, partialTranspose, swapOp,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

set_option maxHeartbeats 2000000 in
theorem productRayE_compression :
    productRayEᴴ * partialTranspose productRayA * productRayE = productRayD := by
  rw [productRayE_adjoint_T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [productRayE, productRayD, productRayL, Matrix.mul_apply,
      Matrix.diagonal_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem productRayD_mul_Dinv : productRayD * productRayDinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [productRayD, productRayDinv, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

theorem productRayD_hermitian : productRayDᴴ = productRayD := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [productRayD, Matrix.conjTranspose_apply, Matrix.diagonal_apply]

theorem productRayDinv_hermitian : productRayDinvᴴ = productRayDinv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [productRayDinv, Matrix.conjTranspose_apply, Matrix.diagonal_apply]

set_option maxHeartbeats 2000000 in
theorem productRayT_hermitian :
    (partialTranspose productRayA)ᴴ = partialTranspose productRayA := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [productRayA, partialTranspose, swapOp, Matrix.conjTranspose_apply,
      Matrix.one_apply]

/-- Preserve the exact `(15/2)^3` normalization when replacing the Werner operator. -/
theorem productRay_endpointOperator_eq :
    endpointOperator = partialTranspose (tripleCopy productRayA) := by
  have hw : werner 3 (1 / 2) = (2 / 15 : ℂ) • productRayA := by
    norm_num [werner, productRayA]
  rw [endpointOperator, hw, tripleCopy_smul, partialTranspose_smul', smul_smul]
  norm_num

/-- Row and column factors, regrouped as three physical pairs. -/
def productRayPairTensor (x d : ProductRayShore → ℂ) : ProductRayThreePairs → ℂ :=
  fun p => x (p.1.1, p.2.1.1, p.2.2.1) * d (p.1.2, p.2.1.2, p.2.2.2)

/-- The literal canonical product-ray rank-two ansatz, without orthogonality restrictions. -/
def productRayMatrix (b x d : ProductRayShore → ℂ) :
    Matrix ProductRayShore ProductRayShore ℂ :=
  fun i j => (if i = (0, 0, 0) then b j else 0) + x i * d j

/-- Regrouping a tensor cube is the repository's `tripleCopy`, with no dimension factor. -/
theorem productRayRectCube_submatrix (M : Matrix ProductRayPair ProductRayPair ℂ) :
    (productRayRectCube M).submatrix (copyEquiv (Fin 3) (Fin 3))
      (copyEquiv (Fin 3) (Fin 3)) = tripleCopy M := rfl

theorem productRay_expectation_cube_regroup (M : Matrix ProductRayPair ProductRayPair ℂ)
    (x d : ProductRayShore → ℂ) :
    expectation (productRayRectCube M) (productRayPairTensor x d) =
      expectation (tripleCopy M) (fun p => x p.1 * d p.2) := by
  rw [← productRayRectCube_submatrix,
    productRay_expectation_submatrix_equiv]
  rfl

/-- Transposing the three opposite-shore factors conjugates `d`, with no transpose of `x`. -/
theorem productRay_expectation_transpose_cube
    (M : Matrix ProductRayPair ProductRayPair ℂ) (x d : ProductRayShore → ℂ) :
    expectation (productRayRectCube (partialTranspose M))
        (productRayPairTensor x (fun i => star (d i))) =
      expectation (productRayRectCube M) (productRayPairTensor x d) := by
  rw [productRay_expectation_cube_regroup, productRay_expectation_cube_regroup,
    ← partialTranspose_tripleCopy]
  simpa only [star_star] using
    expectation_partialTranspose_prod (tripleCopy M) x (fun i => star (d i))

/-- The canonical-ray embedding tensor cube gives exactly the first summand of `C`. -/
theorem productRay_regroup_matrix (b x d : ProductRayShore → ℂ) :
    (fun p => vec (productRayMatrix b x d) ((copyEquiv (Fin 3) (Fin 3)).symm p)) =
      productRayRectCube productRayE *ᵥ b + productRayPairTensor x d := by
  ext ⟨⟨i, j⟩, ⟨k, l⟩, ⟨r, s⟩⟩
  by_cases hi : i = 0 <;> by_cases hk : k = 0 <;> by_cases hr : r = 0 <;>
    simp [vec, productRayMatrix, copyEquiv, productRayPairTensor, productRayRectCube,
      productRayE, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Prod.mk.injEq, hi, hk, hr]

/-- Exact energy binding through the already-proved unnormalized-trace operator identity. -/
theorem productRay_energy_as_expectation (b x d : ProductRayShore → ℂ) :
    (endpointEnergy (productRayMatrix b x d) : ℂ) =
      expectation (productRayRectCube (partialTranspose productRayA))
        (productRayRectCube productRayE *ᵥ b + productRayPairTensor x d) := by
  rw [← expectation_endpointOperator, productRay_endpointOperator_eq,
    partialTranspose_tripleCopy, ← productRayRectCube_submatrix,
    productRay_expectation_submatrix_equiv]
  rw [show vec (productRayMatrix b x d) ∘ (copyEquiv (Fin 3) (Fin 3)).symm =
      productRayRectCube productRayE *ᵥ b + productRayPairTensor x d from
    productRay_regroup_matrix b x d]

/-- Three-site exact Schur completion for an arbitrary source containing `e000`.
The residual is the physical A/B comparison evaluated on `x ⊗ conj(d)`. -/
theorem productRay_energy_completed_square (b x d : ProductRayShore → ℂ) :
    (endpointEnergy (productRayMatrix b x d) : ℂ) =
      expectation (tensor₃ productRayD productRayD productRayD)
        (b + productRayRectCube productRayDinv *ᵥ
          (productRayRectCube productRayL *ᵥ productRayPairTensor x d)) +
      expectation (tensor₃ productRayA productRayA productRayA -
        tensor₃ productRayB productRayB productRayB)
          (productRayPairTensor x (fun i => star (d i))) := by
  have hcompress :
      (productRayRectCube productRayE)ᴴ *
        productRayRectCube (partialTranspose productRayA) * productRayRectCube productRayE =
          productRayRectCube productRayD := by
    rw [← productRayRectCube_conjTranspose, ← productRayRectCube_mul,
      ← productRayRectCube_mul, productRayE_compression]
  have hinverse : productRayRectCube productRayD * productRayRectCube productRayDinv = 1 := by
    rw [← productRayRectCube_mul, productRayD_mul_Dinv, productRayRectCube_one]
  have hcross : (productRayRectCube productRayE)ᴴ *
      productRayRectCube (partialTranspose productRayA) = productRayRectCube productRayL := by
    rw [← productRayRectCube_conjTranspose, ← productRayRectCube_mul,
      productRayE_adjoint_T]
  have hschur : (productRayRectCube productRayL)ᴴ * productRayRectCube productRayDinv *
      productRayRectCube productRayL =
        productRayRectCube (productRayLᴴ * productRayDinv * productRayL) := by
    rw [← productRayRectCube_conjTranspose, ← productRayRectCube_mul,
      ← productRayRectCube_mul]
  rw [productRay_energy_as_expectation]
  rw [productRay_complete_square _ _ _ _
    (productRayRectCube_hermitian _ productRayT_hermitian)
    (productRayRectCube_hermitian _ productRayD_hermitian)
    (productRayRectCube_hermitian _ productRayDinv_hermitian) hcompress hinverse,
    hcross, hschur]
  have hA := productRay_expectation_transpose_cube productRayA x (fun i => star (d i))
  simp only [star_star] at hA
  rw [hA, ← productRay_expectation_transpose_cube
    (productRayLᴴ * productRayDinv * productRayL) x d]
  change expectation (tensor₃ productRayD productRayD productRayD) _ +
    expectation (tensor₃ productRayA productRayA productRayA) _ -
      expectation (tensor₃ productRayB productRayB productRayB) _ = _
  have hsub : ∀ (M N : Matrix ProductRayThreePairs ProductRayThreePairs ℂ) v,
      expectation (M - N) v = expectation M v - expectation N v := by
    intro M N v
    simp only [expectation, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [hsub]
  ring

/-- Real form of the exact completion, suitable for positivity and equality arguments. -/
theorem productRay_energy_completed_square_re (b x d : ProductRayShore → ℂ) :
    endpointEnergy (productRayMatrix b x d) =
      (expectation (tensor₃ productRayD productRayD productRayD)
        (b + productRayRectCube productRayDinv *ᵥ
          (productRayRectCube productRayL *ᵥ productRayPairTensor x d))).re +
      (expectation (tensor₃ productRayA productRayA productRayA -
        tensor₃ productRayB productRayB productRayB)
          (productRayPairTensor x (fun i => star (d i)))).re := by
  have h := congrArg Complex.re (productRay_energy_completed_square b x d)
  simpa only [Complex.ofReal_re, Complex.add_re] using h

end ThreeCopyQutritWerner
