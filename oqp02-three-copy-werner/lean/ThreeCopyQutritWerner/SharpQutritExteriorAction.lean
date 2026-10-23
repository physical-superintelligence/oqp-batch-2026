module

public import ThreeCopyQutritWerner.SharpQutritDoubleAnti
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section


/-!
# Actual local qutrit action on exterior coordinates

The exterior-square action in the fixed cyclic basis is the transpose
adjugate. It is multiplicative, preserves adjoints and actual unitaries, and
is the conjugate defining action times the determinant phase on a unitary.
The final identity binds it to literal local congruence of the wedge matrices.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The local exterior-square action in the literal cyclic qutrit basis. -/
def sharpQutritExteriorAction (U : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ := U.adjugateᵀ

/-- Each exterior action entry is the original oriented two-by-two minor. -/
theorem sharpQutritExteriorAction_apply (U : Matrix (Fin 3) (Fin 3) ℂ)
    (a b : Fin 3) :
    sharpQutritExteriorAction U a b =
      U (sharpQutritWedgeFirst a) (sharpQutritWedgeFirst b) *
        U (sharpQutritWedgeSecond a) (sharpQutritWedgeSecond b) -
      U (sharpQutritWedgeFirst a) (sharpQutritWedgeSecond b) *
        U (sharpQutritWedgeSecond a) (sharpQutritWedgeFirst b) := by
  fin_cases a <;> fin_cases b <;>
    simp [sharpQutritExteriorAction, Matrix.adjugate_fin_three, Matrix.transpose_apply,
      sharpQutritWedgeFirst, sharpQutritWedgeSecond] <;> ring

theorem sharpQutritExteriorAction_one :
    sharpQutritExteriorAction (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
  simp [sharpQutritExteriorAction, Matrix.adjugate_one]

/-- Composition has the original order after transposing the adjugate. -/
theorem sharpQutritExteriorAction_mul (U V : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpQutritExteriorAction (U * V) =
      sharpQutritExteriorAction U * sharpQutritExteriorAction V := by
  simp only [sharpQutritExteriorAction, Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

/-- The exterior action preserves the ordinary complex adjoint. -/
theorem sharpQutritExteriorAction_conjTranspose (U : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpQutritExteriorAction Uᴴ = (sharpQutritExteriorAction U)ᴴ := by
  simp only [sharpQutritExteriorAction, ← Matrix.adjugate_conjTranspose]
  ext i j
  rfl

/-- A literal local unitary induces a literal unitary on all three exterior coordinates. -/
theorem sharpQutritExteriorAction_isometry (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1) :
    (sharpQutritExteriorAction U)ᴴ * sharpQutritExteriorAction U = 1 := by
  rw [← sharpQutritExteriorAction_conjTranspose, ← sharpQutritExteriorAction_mul,
    hU, sharpQutritExteriorAction_one]

/-- On a local unitary, the exterior action is its entrywise conjugate times
the actual determinant. The transpose of the adjoint retains this convention. -/
theorem sharpQutritExteriorAction_of_isometry (U : Matrix (Fin 3) (Fin 3) ℂ)
    (hU : Uᴴ * U = 1) : sharpQutritExteriorAction U = U.det • (Uᴴ)ᵀ := by
  have hUU : U * Uᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hU
  have ha : U.adjugate = U.det • Uᴴ := by
    calc
      U.adjugate = U.adjugate * (U * Uᴴ) := by rw [hUU, Matrix.mul_one]
      _ = (U.adjugate * U) * Uᴴ := by rw [Matrix.mul_assoc]
      _ = (U.det • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Uᴴ := by rw [Matrix.adjugate_mul]
      _ = U.det • Uᴴ := by rw [Matrix.smul_mul, Matrix.one_mul]
  unfold sharpQutritExteriorAction
  rw [ha, Matrix.transpose_smul]

set_option maxRecDepth 2048 in
/-- The cofactor action is exactly the original local congruence of every
fixed wedge basis matrix; this is not an abstract replacement representation. -/
theorem sharpQutritWedgeBasis_congruence (U : Matrix (Fin 3) (Fin 3) ℂ) (a : Fin 3) :
    U * sharpQutritWedgeBasis a * Uᵀ =
      ∑ b, sharpQutritExteriorAction U b a • sharpQutritWedgeBasis b := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [sharpQutritExteriorAction, Matrix.adjugate_fin_three,
      sharpQutritWedgeBasis, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;> ring

end ThreeCopyQutritWerner
