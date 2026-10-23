module

public import VacuumBellSeparation.Gaussian.SymplecticHamiltonian
public import VacuumBellSeparation.Gaussian.ComplexMatrixFunctionalCalculus

@[expose] public section


/-!
# Real positive matrices and orthogonal maps inside complex matrix calculus

Real covariance matrices embed as genuine positive complex matrices by
their actual square-root Gram factorization. Real orthogonal matrices
give actual complex unitaries. Positive square roots and absolute values
then transform by genuine unitary conjugation.
-/

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem complexifyMatrix_one :
    complexifyMatrix (1 : Matrix ι ι ℝ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [complexifyMatrix, Matrix.one_apply, h]

theorem complexifyMatrix_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (complexifyMatrix A).PosSemidef := by
  have hR : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  have he : complexifyMatrix A = complexifyMatrix (CFC.sqrt A) *
      (complexifyMatrix (CFC.sqrt A))ᴴ := by
    rw [← complexifyMatrix_transpose, hR, ← complexifyMatrix_mul,
      CFC.sqrt_mul_sqrt_self A hA.nonneg]
  rw [he]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem complexifyMatrix_isUnit {A : Matrix ι ι ℝ} (hA : IsUnit A) :
    IsUnit (complexifyMatrix A) := by
  apply IsUnit.of_mul_eq_one (complexifyMatrix A⁻¹)
  rw [← complexifyMatrix_mul, A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hA),
    complexifyMatrix_one]

theorem complexifyMatrix_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (complexifyMatrix A).PosDef :=
  (complexifyMatrix_posSemidef hA.posSemidef).posDef_iff_isUnit.mpr
    (complexifyMatrix_isUnit hA.isUnit)

def orthogonalComplexUnitary (O : Matrix ι ι ℝ) (hO : Oᵀ * O = 1) :
    unitary (Matrix ι ι ℂ) :=
  ⟨complexifyMatrix O, by
    have hO' : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
    constructor
    · change (complexifyMatrix O)ᴴ * complexifyMatrix O = 1
      rw [← complexifyMatrix_transpose, ← complexifyMatrix_mul, hO, complexifyMatrix_one]
    · change complexifyMatrix O * (complexifyMatrix O)ᴴ = 1
      rw [← complexifyMatrix_transpose, ← complexifyMatrix_mul, hO', complexifyMatrix_one]⟩

@[simp] theorem orthogonalComplexUnitary_coe (O : Matrix ι ι ℝ) (hO : Oᵀ * O = 1) :
    (orthogonalComplexUnitary O hO : Matrix ι ι ℂ) = complexifyMatrix O := rfl

theorem complex_matrix_sqrt_unitary_conjugate (U : unitary (Matrix ι ι ℂ))
    {A : Matrix ι ι ℂ} (hA : 0 ≤ A) :
    CFC.sqrt ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * CFC.sqrt A * (U : Matrix ι ι ℂ)ᴴ := by
  have hU : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 := U.property.1
  have hpos : 0 ≤ (U : Matrix ι ι ℂ) * CFC.sqrt A * (U : Matrix ι ι ℂ)ᴴ :=
    ((CFC.sqrt_nonneg A).posSemidef.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)).nonneg
  apply CFC.sqrt_unique (hb := hpos)
  calc
    _ = (U : Matrix ι ι ℂ) * (CFC.sqrt A *
        ((U : Matrix ι ι ℂ)ᴴ * U) * CFC.sqrt A) * (U : Matrix ι ι ℂ)ᴴ := by noncomm_ring
    _ = _ := by
      rw [hU, Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA]

theorem complex_matrix_abs_unitary_conjugate (U : unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) :
    CFC.abs ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * CFC.abs A * (U : Matrix ι ι ℂ)ᴴ := by
  have hU : (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 := U.property.1
  have hg : ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)ᴴ *
      ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
        (U : Matrix ι ι ℂ) * (Aᴴ * A) * (U : Matrix ι ι ℂ)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = (U : Matrix ι ι ℂ) * Aᴴ * ((U : Matrix ι ι ℂ)ᴴ * U) * A *
          (U : Matrix ι ι ℂ)ᴴ := by noncomm_ring
      _ = _ := by rw [hU, Matrix.mul_one]; noncomm_ring
  simp only [CFC.abs, Matrix.star_eq_conjTranspose]
  rw [hg, complex_matrix_sqrt_unitary_conjugate U (Matrix.posSemidef_conjTranspose_mul_self A).nonneg]

end VacuumBellSeparation.Gaussian
