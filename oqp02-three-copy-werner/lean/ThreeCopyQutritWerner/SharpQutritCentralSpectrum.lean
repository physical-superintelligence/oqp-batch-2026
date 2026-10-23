module

public import ThreeCopyQutritWerner.SharpQutritDoubleAnti
public import ThreeCopyQutritWerner.SingularValueRank

@[expose] public section


/-!
# Exact spectral invariants of the physical qutrit central block

These are the actual Hermitian eigenvalues of the central block already
identified inside the double-antisymmetric diagonal normal form. No chosen
roots or assumed diagonalization enter the statements.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Real exterior coefficients give a Hermitian physical central block. -/
theorem sharpQutritCentralBlock_isHermitian (d : Fin 3 → ℝ) :
    (sharpQutritCentralBlock (fun i => (d i : ℂ))).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharpQutritCentralBlock, Matrix.conjTranspose_apply, Complex.star_def]

/-- The physical central block has zero trace. -/
theorem sharpQutritCentralBlock_trace (d : Fin 3 → ℝ) :
    (sharpQutritCentralBlock (fun i => (d i : ℂ))).trace = 0 := by
  simp [Matrix.trace, sharpQutritCentralBlock, Fin.sum_univ_three]

/-- Its squared Frobenius norm is twice the squared coefficient norm. -/
theorem sharpQutritCentralBlock_frobSq (d : Fin 3 → ℝ) :
    frobSq (sharpQutritCentralBlock (fun i => (d i : ℂ))) =
      2 * ∑ i, d i ^ 2 := by
  simp [frobSq, sharpQutritCentralBlock, Fin.sum_univ_three,
    Complex.normSq_ofReal]
  ring

/-- The actual central eigenvalues, with the pinned spectral theorem's
original indexing. This definition does not claim that those indices are sorted. -/
def sharpQutritCentralEigenvalue (d : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (sharpQutritCentralBlock_isHermitian d).eigenvalues

/-- The three actual central eigenvalues sum to zero. -/
theorem sharpQutritCentralEigenvalue_sum (d : Fin 3 → ℝ) :
    ∑ i, sharpQutritCentralEigenvalue d i = 0 := by
  have h := (sharpQutritCentralBlock_isHermitian d).trace_eq_sum_eigenvalues
  rw [sharpQutritCentralBlock_trace] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_zero, sharpQutritCentralEigenvalue,
    RCLike.ofReal_eq_complex_ofReal] using! h.symm

/-- The product of the actual central eigenvalues detects the three exterior
directions through the original determinant, with its exact factor two. -/
theorem sharpQutritCentralEigenvalue_prod (d : Fin 3 → ℝ) :
    ∏ i, sharpQutritCentralEigenvalue d i = 2 * d 0 * d 1 * d 2 := by
  have h := (sharpQutritCentralBlock_isHermitian d).det_eq_prod_eigenvalues
  rw [sharpQutritCentralBlock_det] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_prod, Complex.ofReal_mul, Complex.ofReal_ofNat,
    sharpQutritCentralEigenvalue, RCLike.ofReal_eq_complex_ofReal] using! h.symm

/-- The actual Hermitian eigenvalues account for the entire Frobenius norm. -/
theorem hermitian_frobSq_eq_sum_eigenvalues_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    frobSq H = ∑ i, hH.eigenvalues i ^ 2 := by
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hfac : H = U * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, U, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose]
      using! hH.spectral_theorem
  calc
    frobSq H = frobSq (U * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ) :=
      congrArg frobSq hfac
    _ = frobSq (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))) := by
      rw [Matrix.mul_assoc, nuclearTrace_frobSq_isometry_mul _ _ hU,
        ← singular_frobSq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, nuclearTrace_frobSq_isometry_mul _ _ hU,
        singular_frobSq_conjTranspose]
    _ = _ := by
      simp [frobSq, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]

/-- The central eigenvalue squares sum to twice the squared exterior coefficients. -/
theorem sharpQutritCentralEigenvalue_sum_sq (d : Fin 3 → ℝ) :
    ∑ i, sharpQutritCentralEigenvalue d i ^ 2 = 2 * ∑ i, d i ^ 2 := by
  rw [sharpQutritCentralEigenvalue,
    ← hermitian_frobSq_eq_sum_eigenvalues_sq _ (sharpQutritCentralBlock_isHermitian d),
    sharpQutritCentralBlock_frobSq]

/-- Any zero actual central eigenvalue forces a vanishing original exterior
coefficient, by the exact determinant identity. -/
theorem sharpQutritCentralEigenvalue_zero_forces_coefficient_zero
    (d : Fin 3 → ℝ) (i : Fin 3) (hi : sharpQutritCentralEigenvalue d i = 0) :
    d 0 = 0 ∨ d 1 = 0 ∨ d 2 = 0 := by
  have hp : ∏ j, sharpQutritCentralEigenvalue d j = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [sharpQutritCentralEigenvalue_prod] at hp
  rcases mul_eq_zero.mp hp with h01 | h2
  · rcases mul_eq_zero.mp h01 with h0 | h1
    · exact Or.inl ((mul_eq_zero.mp h0).resolve_left (by norm_num))
    · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

end ThreeCopyQutritWerner
