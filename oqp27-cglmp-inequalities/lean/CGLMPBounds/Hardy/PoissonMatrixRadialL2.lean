module

public import CGLMPBounds.Hardy.PoissonScalarRadialL2
public import CGLMPBounds.Hardy.MatrixCoordinateL2

@[expose] public section


/-! Actual matrix radial convergence, first in the normalized HS norm and
then in the actual Hilbert operator norm. Finite sums carry the scalar L²
limits; an explicit coordinate constant controls the operator norm. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma matrixHilbert_memLp_operator {r : ℕ} (B : UnitCircle → Circulation.Mat r) :
    MemLp (matrixHilbert B) 2 circleMeasure := by
  apply matrix_memLp_of_entries
  intro i j
  exact scalarHilbert_memLp (fun t => B t i j)

lemma matrixPoissonRadial_memLp_operator {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    MemLp (matrixPoissonRadial B ρ) 2 circleMeasure := by
  apply matrix_memLp_of_entries
  intro i j
  exact scalarPoissonRadial_memLp ((matrix_memLp_entries hB i j).integrable (by norm_num)) hρ

lemma matrixPoissonRadial_error_memLp {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure) {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) :
    MemLp (fun t => matrixPoissonRadial B ρ t - (B t+Complex.I • matrixHilbert B t))
      2 circleMeasure :=
  (matrixPoissonRadial_memLp_operator hB hρ).sub
    (hB.add ((matrixHilbert_memLp_operator B).const_smul Complex.I))

set_option maxHeartbeats 1000000 in
lemma matrixPoissonRadial_coordinate_error_tendsto {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure) :
    Tendsto (fun ρ : ℝ => ∑ ij : Fin r × Fin r,
      ∫ t, ‖(matrixPoissonRadial B ρ t -
        (B t+Complex.I • matrixHilbert B t)) ij.1 ij.2‖^2 ∂circleMeasure)
      (𝓝[<] 1) (𝓝 0) := by
  have ht := tendsto_finset_sum Finset.univ (fun (ij : Fin r × Fin r) _ =>
    scalarPoissonRadial_L2_tendsto (matrix_memLp_entries hB ij.1 ij.2))
  simpa only [Finset.sum_const_zero,scalarPoissonIntegral,matrixPoissonAnalytic,
    matrixPoissonRadial,matrixHilbert,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul] using ht

theorem matrixPoissonRadial_HS_tendsto {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure) :
    Tendsto (fun ρ : ℝ => ∫ t, Circulation.hsSq
      (matrixPoissonRadial B ρ t - (B t+Complex.I • matrixHilbert B t)) ∂circleMeasure)
      (𝓝[<] 1) (𝓝 0) := by
  have ht := (matrixPoissonRadial_coordinate_error_tendsto hB).div_const (r : ℝ)
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ρ hρ
  have hm := matrixPoissonRadial_error_memLp hB ⟨hρ.1.le,hρ.2⟩
  simp_rw [matrix_hsSq_eq_entry_norm_sq]
  rw [integral_div]
  congr 1
  have he := (integral_finset_sum Finset.univ (fun (ij : Fin r × Fin r) _ =>
    (matrix_memLp_entries hm ij.1 ij.2).integrable_norm_pow (by norm_num))).symm
  simpa only [Fintype.sum_prod_type] using he

theorem matrixPoissonRadial_operator_L2_tendsto {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure) :
    Tendsto (fun ρ : ℝ => ∫ t,
      ‖matrixPoissonRadial B ρ t - (B t+Complex.I • matrixHilbert B t)‖^2 ∂circleMeasure)
      (𝓝[<] 1) (𝓝 0) := by
  have ht := (matrixPoissonRadial_coordinate_error_tendsto hB).const_mul
    (matrixCoordinateSquareConstant r)
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · exact Eventually.of_forall fun ρ => integral_nonneg (fun _ => sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ρ hρ
    exact matrix_operator_square_integral_bound
      (matrixPoissonRadial_error_memLp hB ⟨hρ.1.le,hρ.2⟩)

end
end CGLMPBounds.Hardy
