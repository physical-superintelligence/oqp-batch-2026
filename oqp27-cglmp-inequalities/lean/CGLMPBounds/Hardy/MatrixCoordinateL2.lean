module

public import CGLMPBounds.Hardy.MatrixEntryIntegration
public import CGLMPBounds.Hardy.CircleMatrixL2

@[expose] public section


/-! Explicit finite-coordinate control of the Hilbert operator norm.
This supplies norm-independent transfers from scalar Fourier L² estimates
to matrix L² estimates, rather than identifying different matrix norms. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma matrix_eq_sum_entries {r : ℕ} (X : Circulation.Mat r) :
    X = ∑ ij : Fin r × Fin r, X ij.1 ij.2 • Matrix.single ij.1 ij.2 1 := by
  ext i j
  simp [Fintype.sum_prod_type,Matrix.sum_apply,Matrix.single_apply,ite_and]

def matrixCoordinateSquareConstant (r : ℕ) : ℝ :=
  ∑ ij : Fin r × Fin r, ‖(Matrix.single ij.1 ij.2 1 : Circulation.Mat r)‖^2

lemma matrixCoordinateSquareConstant_nonneg (r : ℕ) : 0 ≤ matrixCoordinateSquareConstant r :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma matrix_operator_sq_le_coordinate_sq {r : ℕ} (X : Circulation.Mat r) :
    ‖X‖^2 ≤ matrixCoordinateSquareConstant r * ∑ ij : Fin r × Fin r, ‖X ij.1 ij.2‖^2 := by
  have hn : ‖X‖ ≤ ∑ ij : Fin r × Fin r,
      ‖X ij.1 ij.2‖ * ‖(Matrix.single ij.1 ij.2 1 : Circulation.Mat r)‖ := by
    calc
      _ = ‖∑ ij : Fin r × Fin r, X ij.1 ij.2 • Matrix.single ij.1 ij.2 1‖ :=
        congrArg norm (matrix_eq_sum_entries X)
      _ ≤ ∑ ij : Fin r × Fin r,
          ‖(X ij.1 ij.2 • Matrix.single ij.1 ij.2 1 : Circulation.Mat r)‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro ij _
        exact norm_smul _ _
  calc
    _ ≤ (∑ ij : Fin r × Fin r,
        ‖X ij.1 ij.2‖ * ‖(Matrix.single ij.1 ij.2 1 : Circulation.Mat r)‖)^2 := by
      nlinarith [norm_nonneg X]
    _ ≤ _ := by
      simpa only [matrixCoordinateSquareConstant,mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun ij : Fin r × Fin r => ‖X ij.1 ij.2‖)
          (fun ij : Fin r × Fin r => ‖(Matrix.single ij.1 ij.2 1 : Circulation.Mat r)‖)

lemma matrix_memLp_of_entries {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r : ℕ} {F : α → Circulation.Mat r}
    (hF : ∀ i j, MemLp (fun t => F t i j) 2 μ) : MemLp F 2 μ := by
  have he : F = fun t => ∑ ij : Fin r × Fin r,
      F t ij.1 ij.2 • Matrix.single ij.1 ij.2 1 := funext (fun t => matrix_eq_sum_entries (F t))
  rw [he]
  apply memLp_finsetSum
  intro ij _
  let L : ℂ →L[ℂ] Circulation.Mat r :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (Matrix.single ij.1 ij.2 1)
  exact L.comp_memLp' (hF ij.1 ij.2)

lemma matrix_memLp_entries {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r : ℕ} {F : α → Circulation.Mat r} (hF : MemLp F 2 μ) (i j : Fin r) :
    MemLp (fun t => F t i j) 2 μ := (matrixEntryCLM i j).comp_memLp' hF

lemma matrix_operator_square_integral_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r : ℕ} {F : α → Circulation.Mat r} (hF : MemLp F 2 μ) :
    (∫ t, ‖F t‖^2 ∂μ) ≤ matrixCoordinateSquareConstant r *
      ∑ ij : Fin r × Fin r, (∫ t, ‖F t ij.1 ij.2‖^2 ∂μ) := by
  have heint (ij : Fin r × Fin r) : Integrable (fun t => ‖F t ij.1 ij.2‖^2) μ :=
    (matrix_memLp_entries hF ij.1 ij.2).integrable_norm_pow (by norm_num)
  rw [← integral_finset_sum _ (fun ij _ => heint ij),← integral_const_mul]
  apply integral_mono (hF.integrable_norm_pow (by norm_num))
    ((integrable_finsetSum _ (fun ij _ => heint ij)).const_mul _)
  intro t
  exact matrix_operator_sq_le_coordinate_sq (F t)

end
end CGLMPBounds.Hardy
