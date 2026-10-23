module

public import ThreeCopyQutritWerner.ZeroReserveAlgebra
public import ThreeCopyQutritWerner.SingularValueRank

@[expose] public section


/-!
# Literal partial traces as complex linear maps

These six maps keep exactly the repository's unnormalized three-site
contractions. Their linearity and adjoint transport support coherent-pencil
identities without any change of physical coordinates.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- The literal unnormalized partial trace, as a complex linear map. -/
def ptrace₁LinearMap :
    Matrix (a × b × c) (a × b × c) ℂ →ₗ[ℂ] Matrix (b × c) (b × c) ℂ where
  toFun := ptrace₁
  map_add' A B := by
    ext i j
    simp [ptrace₁, Finset.sum_add_distrib]
  map_smul' z A := by
    ext i j
    simp [ptrace₁, Finset.mul_sum]

/-- Literal partial tracing commutes with the actual complex adjoint. -/
theorem ptrace₁_conjTranspose
    (A : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁ Aᴴ = (ptrace₁ A)ᴴ := by
  ext i j
  simp only [ptrace₁, Matrix.conjTranspose_apply, Complex.star_def, map_sum]

/-- The literal unnormalized partial trace, as a complex linear map. -/
def ptrace₂LinearMap :
    Matrix (a × b × c) (a × b × c) ℂ →ₗ[ℂ] Matrix (a × c) (a × c) ℂ where
  toFun := ptrace₂
  map_add' A B := by
    ext i j
    simp [ptrace₂, Finset.sum_add_distrib]
  map_smul' z A := by
    ext i j
    simp [ptrace₂, Finset.mul_sum]

/-- Literal partial tracing commutes with the actual complex adjoint. -/
theorem ptrace₂_conjTranspose
    (A : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂ Aᴴ = (ptrace₂ A)ᴴ := by
  ext i j
  simp only [ptrace₂, Matrix.conjTranspose_apply, Complex.star_def, map_sum]

/-- The literal unnormalized partial trace, as a complex linear map. -/
def ptrace₃LinearMap :
    Matrix (a × b × c) (a × b × c) ℂ →ₗ[ℂ] Matrix (a × b) (a × b) ℂ where
  toFun := ptrace₃
  map_add' A B := by
    ext i j
    simp [ptrace₃, Finset.sum_add_distrib]
  map_smul' z A := by
    ext i j
    simp [ptrace₃, Finset.mul_sum]

/-- Literal partial tracing commutes with the actual complex adjoint. -/
theorem ptrace₃_conjTranspose
    (A : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₃ Aᴴ = (ptrace₃ A)ᴴ := by
  ext i j
  simp only [ptrace₃, Matrix.conjTranspose_apply, Complex.star_def, map_sum]

/-- The literal unnormalized partial trace, as a complex linear map. -/
def ptrace₁₂LinearMap :
    Matrix (a × b × c) (a × b × c) ℂ →ₗ[ℂ] Matrix (c) (c) ℂ where
  toFun := ptrace₁₂
  map_add' A B := by
    ext i j
    simp [ptrace₁₂, Finset.sum_add_distrib]
  map_smul' z A := by
    ext i j
    simp [ptrace₁₂, Finset.mul_sum]

/-- Literal partial tracing commutes with the actual complex adjoint. -/
theorem ptrace₁₂_conjTranspose
    (A : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₂ Aᴴ = (ptrace₁₂ A)ᴴ := by
  ext i j
  simp only [ptrace₁₂, Matrix.conjTranspose_apply, Complex.star_def, map_sum]

/-- The literal unnormalized partial trace, as a complex linear map. -/
def ptrace₁₃LinearMap :
    Matrix (a × b × c) (a × b × c) ℂ →ₗ[ℂ] Matrix (b) (b) ℂ where
  toFun := ptrace₁₃
  map_add' A B := by
    ext i j
    simp [ptrace₁₃, Finset.sum_add_distrib]
  map_smul' z A := by
    ext i j
    simp [ptrace₁₃, Finset.mul_sum]

/-- Literal partial tracing commutes with the actual complex adjoint. -/
theorem ptrace₁₃_conjTranspose
    (A : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₁₃ Aᴴ = (ptrace₁₃ A)ᴴ := by
  ext i j
  simp only [ptrace₁₃, Matrix.conjTranspose_apply, Complex.star_def, map_sum]

/-- The literal unnormalized partial trace, as a complex linear map. -/
def ptrace₂₃LinearMap :
    Matrix (a × b × c) (a × b × c) ℂ →ₗ[ℂ] Matrix (a) (a) ℂ where
  toFun := ptrace₂₃
  map_add' A B := by
    ext i j
    simp [ptrace₂₃, Finset.sum_add_distrib]
  map_smul' z A := by
    ext i j
    simp [ptrace₂₃, Finset.mul_sum]

/-- Literal partial tracing commutes with the actual complex adjoint. -/
theorem ptrace₂₃_conjTranspose
    (A : Matrix (a × b × c) (a × b × c) ℂ) :
    ptrace₂₃ Aᴴ = (ptrace₂₃ A)ᴴ := by
  ext i j
  simp only [ptrace₂₃, Matrix.conjTranspose_apply, Complex.star_def, map_sum]

end ThreeCopyQutritWerner

