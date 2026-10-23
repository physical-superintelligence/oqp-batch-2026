module

public import ThreeCopyQutritWerner.SharpDoubleAntisymmetric

@[expose] public section


/-!
# Exact qutrit coordinates of the double-antisymmetric range

The Levi-Civita coordinate matrix is an exact parametrization of the literal
projection range. Its Frobenius scale is four. For diagonal coefficients,
the physical diagonal coordinates carry a three-by-three zero-diagonal block;
the other coordinates form three independent two-by-two blocks.

This module proves coordinate algebra only. It does not assume a local-unitary
normal form or claim the remaining sharp-PT equality classification.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- The three unnormalized, consistently oriented qutrit exterior basis matrices. -/
def sharpQutritWedgeBasis : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, 0, 0; 0, 0, 1; 0, -1, 0],
    !![0, 0, -1; 0, 0, 0; 1, 0, 0],
    !![0, 1, 0; -1, 0, 0; 0, 0, 0]]

/-- The first coordinate of each cyclicly oriented exterior basis pair. -/
def sharpQutritWedgeFirst : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The second coordinate of each cyclicly oriented exterior basis pair. -/
def sharpQutritWedgeSecond : Fin 3 → Fin 3 := ![2, 0, 1]

/-- Encode the nine complex exterior coefficients as an actual physical matrix. -/
def sharpQutritAntiEncode (K : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun i j => ∑ a, ∑ b, sharpQutritWedgeBasis a i.1 j.1 * K a b *
    sharpQutritWedgeBasis b i.2 j.2

/-- Extract the nine positively oriented physical entries, with no rescaling. -/
def sharpQutritAntiCoefficients (Z : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun a b => Z (sharpQutritWedgeFirst a, sharpQutritWedgeFirst b)
    (sharpQutritWedgeSecond a, sharpQutritWedgeSecond b)

/-- All original coefficient entries are recovered exactly. -/
theorem sharpQutritAntiCoefficients_encode (K : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpQutritAntiCoefficients (sharpQutritAntiEncode K) = K := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sharpQutritAntiCoefficients, sharpQutritAntiEncode,
      sharpQutritWedgeFirst, sharpQutritWedgeSecond, sharpQutritWedgeBasis,
      Fin.sum_univ_three]

set_option maxRecDepth 2048 in
/-- Every encoded coefficient matrix lies in the literal projection range. -/
theorem sharpQutritAntiEncode_fixed (K : Matrix (Fin 3) (Fin 3) ℂ) :
    sharpDoubleAnti (sharpQutritAntiEncode K) = sharpQutritAntiEncode K := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, sharpQutritAntiEncode,
      sharpQutritWedgeBasis, Fin.sum_univ_three] <;> ring

set_option maxRecDepth 2048 in
/-- The coefficients reconstruct every projected physical matrix exactly. -/
theorem sharpQutritAntiEncode_projected_coefficients
    (Z : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    sharpQutritAntiEncode (sharpQutritAntiCoefficients (sharpDoubleAnti Z)) =
      sharpDoubleAnti Z := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, sharpQutritAntiEncode,
      sharpQutritAntiCoefficients, sharpQutritWedgeFirst, sharpQutritWedgeSecond,
      sharpQutritWedgeBasis, Fin.sum_univ_three] <;> ring

/-- A complete parametrization of the physical double-antisymmetric range. -/
theorem sharpQutritAntiEncode_coefficients_iff
    (Z : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    sharpDoubleAnti Z = Z ↔ sharpQutritAntiEncode (sharpQutritAntiCoefficients Z) = Z := by
  constructor
  · intro h
    simpa only [h] using sharpQutritAntiEncode_projected_coefficients Z
  · intro h
    rw [← h]
    exact sharpQutritAntiEncode_fixed _

set_option maxRecDepth 2048 in
/-- The original unnormalized exterior coordinates have exact squared-norm scale four. -/
theorem sharpQutritAntiEncode_frobSq (K : Matrix (Fin 3) (Fin 3) ℂ) :
    frobSq (sharpQutritAntiEncode K) = 4 * frobSq K := by
  simp [frobSq, Fintype.sum_prod_type, sharpQutritAntiEncode,
    sharpQutritWedgeBasis, Fin.sum_univ_three]
  ring

/-- Central block on the physical diagonal coordinates for diagonal coefficients. -/
def sharpQutritCentralBlock (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, z 2, z 1; z 2, 0, z 0; z 1, z 0, 0]

/-- The missing qutrit coordinate for distinct indices; diagonal values are unused. -/
def sharpQutritMissing : Fin 3 → Fin 3 → Fin 3 :=
  ![![0, 2, 1], ![2, 0, 0], ![1, 0, 0]]

/-- The three physical diagonal coordinates carry precisely the central block. -/
theorem sharpQutritAntiEncode_diagonal_block (z : Fin 3 → ℂ) :
    (sharpQutritAntiEncode (Matrix.diagonal z)).submatrix (fun i => (i, i))
      (fun i => (i, i)) = sharpQutritCentralBlock z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharpQutritAntiEncode, sharpQutritWedgeBasis, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.submatrix_apply, sharpQutritCentralBlock]

set_option maxRecDepth 2048 in
/-- The complete action: one three-dimensional central block and three
off-diagonal coordinate pairs, each with coefficient minus the missing entry. -/
theorem sharpQutritAntiEncode_diagonal_action (z : Fin 3 → ℂ)
    (v : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) :
    (sharpQutritAntiEncode (Matrix.diagonal z) *ᵥ v) (i, j) =
      if i = j then (sharpQutritCentralBlock z *ᵥ (fun k => v (k, k))) i
      else -z (sharpQutritMissing i j) * v (j, i) := by
  fin_cases i <;> fin_cases j <;>
    simp [sharpQutritAntiEncode, sharpQutritWedgeBasis, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      sharpQutritCentralBlock, sharpQutritMissing] <;> ring

/-- The central determinant detects a nonzero coefficient in every exterior direction. -/
theorem sharpQutritCentralBlock_det (z : Fin 3 → ℂ) :
    (sharpQutritCentralBlock z).det = 2 * z 0 * z 1 * z 2 := by
  simp [sharpQutritCentralBlock, Matrix.det_fin_three]
  ring

end ThreeCopyQutritWerner
