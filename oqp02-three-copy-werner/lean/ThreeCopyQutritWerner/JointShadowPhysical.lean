module

public import ThreeCopyQutritWerner.JointShadowContractions

@[expose] public section


/-! Actual common purifications and all seven nonempty physical marginals.
The same logical columns are retained in every grouping. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

variable {l a b c : Type*}

/-- The original source columns, with the logical register placed first. -/
def jointShadowPurification (X : Matrix (a × b × c) l ℂ) : l × a × b × c → ℂ :=
  fun p => X p.2 p.1

/-- Group physical subsystem A first, preserving every original coordinate. -/
def jointShadowSplitA : (l × a × b × c) ≃ a × (l × b × c) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group physical subsystem B first, preserving every original coordinate. -/
def jointShadowSplitB : (l × a × b × c) ≃ b × (l × a × c) where
  toFun p := (p.2.2.1, p.1, p.2.1, p.2.2.2)
  invFun p := (p.2.1, p.2.2.1, p.1, p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group physical subsystem C first, preserving every original coordinate. -/
def jointShadowSplitC : (l × a × b × c) ≃ c × (l × a × b) where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun p := (p.2.1, p.2.2.1, p.2.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group physical subsystem AB first, preserving every original coordinate. -/
def jointShadowSplitAB : (l × a × b × c) ≃ (a × b) × (l × c) where
  toFun p := ((p.2.1, p.2.2.1), (p.1, p.2.2.2))
  invFun p := (p.2.1, p.1.1, p.1.2, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group physical subsystem AC first, preserving every original coordinate. -/
def jointShadowSplitAC : (l × a × b × c) ≃ (a × c) × (l × b) where
  toFun p := ((p.2.1, p.2.2.2), (p.1, p.2.2.1))
  invFun p := (p.2.1, p.1.1, p.2.2, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group physical subsystem BC first, preserving every original coordinate. -/
def jointShadowSplitBC : (l × a × b × c) ≃ (b × c) × (l × a) where
  toFun p := ((p.2.2.1, p.2.2.2), (p.1, p.2.1))
  invFun p := (p.2.1, p.2.2, p.1.1, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group physical subsystem ABC first, preserving every original coordinate. -/
def jointShadowSplitABC : (l × a × b × c) ≃ (a × b × c) × l where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype l] [Fintype a] [Fintype b] [Fintype c]

/-- The literal reduction onto the first grouped subsystem of the common purification. -/
def jointShadowReduced {u v : Type*} [Fintype u] [Fintype v]
    (e : (l × a × b × c) ≃ u × v)
    (X Y : Matrix (a × b × c) l ℂ) : Matrix u u ℂ :=
  ptraceR (ketBra (jointShadowPurification X ∘ e.symm)
    (jointShadowPurification Y ∘ e.symm))

/-- The A grouped reduction is exactly the existing unnormalized physical marginal. -/
theorem jointShadowReduced_A (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowReduced jointShadowSplitA X Y = ptrace₂₃ (X * Yᴴ) := by
  ext i j
  simp only [jointShadowReduced, ptraceR, ketBra, jointShadowPurification,
    jointShadowSplitA, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk,
    Function.comp_apply, Fintype.sum_prod_type,
    ptrace₂₃, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- The B grouped reduction is exactly the existing unnormalized physical marginal. -/
theorem jointShadowReduced_B (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowReduced jointShadowSplitB X Y = ptrace₁₃ (X * Yᴴ) := by
  ext i j
  simp only [jointShadowReduced, ptraceR, ketBra, jointShadowPurification,
    jointShadowSplitB, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk,
    Function.comp_apply, Fintype.sum_prod_type,
    ptrace₁₃, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- The C grouped reduction is exactly the existing unnormalized physical marginal. -/
theorem jointShadowReduced_C (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowReduced jointShadowSplitC X Y = ptrace₁₂ (X * Yᴴ) := by
  ext i j
  simp only [jointShadowReduced, ptraceR, ketBra, jointShadowPurification,
    jointShadowSplitC, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk,
    Function.comp_apply, Fintype.sum_prod_type,
    ptrace₁₂, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

/-- The AB grouped reduction is exactly the existing unnormalized physical marginal. -/
theorem jointShadowReduced_AB (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowReduced jointShadowSplitAB X Y = ptrace₃ (X * Yᴴ) := by
  ext i j
  simp only [jointShadowReduced, ptraceR, ketBra, jointShadowPurification,
    jointShadowSplitAB, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk,
    Function.comp_apply, Fintype.sum_prod_type,
    ptrace₃, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]

/-- The AC grouped reduction is exactly the existing unnormalized physical marginal. -/
theorem jointShadowReduced_AC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowReduced jointShadowSplitAC X Y = ptrace₂ (X * Yᴴ) := by
  ext i j
  simp only [jointShadowReduced, ptraceR, ketBra, jointShadowPurification,
    jointShadowSplitAC, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk,
    Function.comp_apply, Fintype.sum_prod_type,
    ptrace₂, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]

/-- The BC grouped reduction is exactly the existing unnormalized physical marginal. -/
theorem jointShadowReduced_BC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowReduced jointShadowSplitBC X Y = ptrace₁ (X * Yᴴ) := by
  ext i j
  simp only [jointShadowReduced, ptraceR, ketBra, jointShadowPurification,
    jointShadowSplitBC, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk,
    Function.comp_apply, Fintype.sum_prod_type,
    ptrace₁, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [Finset.sum_comm]

/-- The ABC grouped reduction is exactly the existing unnormalized physical marginal. -/
theorem jointShadowReduced_ABC (X Y : Matrix (a × b × c) l ℂ) :
    jointShadowReduced jointShadowSplitABC X Y = X * Yᴴ := by
  ext i j
  simp only [jointShadowReduced, ptraceR, ketBra, jointShadowPurification,
    jointShadowSplitABC, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk,
    Function.comp_apply, Fintype.sum_prod_type,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]

end ThreeCopyQutritWerner
