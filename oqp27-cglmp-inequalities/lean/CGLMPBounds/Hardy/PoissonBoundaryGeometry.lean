module

public import CGLMPBounds.Hardy.PoissonMatrixRadialL2
public import CGLMPBounds.Hardy.PoissonTraceMean
public import CGLMPBounds.Hardy.HardyMatrixPotentialNormBound

@[expose] public section


/-! The actual Poisson boundary lies in a closed real-part contraction set.
The literal matrix root potential is continuous there and has linear growth.
This file also makes every matrix norm transfer through scalar coordinates. -/
namespace CGLMPBounds.Hardy
noncomputable section
open MeasureTheory Filter Set Matrix
open scoped Topology
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Entrywise
open scoped Matrix.Norms.Elementwise
local instance poissonBoundaryGeometryENormedAddMonoid {r : ℕ} :
    ENormedAddMonoid (Circulation.Mat r) :=
  inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))

lemma matrixHilbert_hermitian_of_entries {r : ℕ}
    (B : UnitCircle → Circulation.Mat r)
    (hB : ∀ i j, MemLp (fun t => B t i j) 2 circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian) :
    ∀ᵐ t ∂circleMeasure, (matrixHilbert B t).IsHermitian := by
  apply matrixHilbert_hermitian_ae B _ hherm
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  exact hB i j
end Entrywise

section Operator
open scoped Matrix.Norms.L2Operator

lemma hermitianRealPart_norm_le {r : ℕ} (X : Circulation.Mat r) :
    ‖hermitianRealPart X‖ ≤ ‖X‖ := by
  have hstar : ‖Xᴴ‖=‖X‖ := norm_star X
  calc
    _ = (1/2 : ℝ)*‖X+Xᴴ‖ := by
      rw [hermitianRealPart,norm_smul]
      norm_num
    _ ≤ (1/2 : ℝ)*(‖X‖+‖Xᴴ‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by rw [hstar]; ring

lemma hermitianImagPart_norm_le {r : ℕ} (X : Circulation.Mat r) :
    ‖hermitianImagPart X‖ ≤ ‖X‖ := by
  have hstar : ‖Xᴴ‖=‖X‖ := norm_star X
  calc
    _ = (1/2 : ℝ)*‖X-Xᴴ‖ := by
      rw [hermitianImagPart,norm_smul,norm_div,norm_neg,Complex.norm_I]
      norm_num
    _ ≤ (1/2 : ℝ)*(‖X‖+‖Xᴴ‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = _ := by rw [hstar]; ring

lemma isClosed_realPart_contractions (r : ℕ) :
    IsClosed {X : Circulation.Mat r | ‖hermitianRealPart X‖ ≤ 1} :=
  isClosed_le (hermitianRealPartCLM (r := r)).continuous.norm continuous_const

lemma continuousOn_matrixHardyPotential_realPart_contractions (r : ℕ) :
    ContinuousOn (matrixHardyPotential (ι := Fin r))
      {X : Circulation.Mat r | ‖hermitianRealPart X‖ ≤ 1} := by
  apply continuousOn_matrixHardyPotential_closed_spectrum.mono
  intro X hX z hz
  exact (matrix_spectrum_parts_rectangle X hz).1.trans hX

lemma matrixHardyPotential_linear_growth {r : ℕ} (hr : 0 < r)
    {X : Circulation.Mat r} (hX : ‖hermitianRealPart X‖ ≤ 1) :
    |matrixHardyPotential X| ≤ (|hardyStripCenterConstant|+1)*(1+‖X‖) := by
  have hu := matrixHardyPotential_norm_bound hr X
    (fun z hz => (matrix_spectrum_parts_rectangle X hz).1.trans hX)
  rw [abs_of_nonneg hu.1]
  have hi := hermitianImagPart_norm_le X
  have hc := le_abs_self hardyStripCenterConstant
  have hp := mul_nonneg (abs_nonneg hardyStripCenterConstant) (norm_nonneg X)
  nlinarith

lemma circle_bounded_matrix_memLp {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : AEStronglyMeasurable B circleMeasure)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1) : MemLp B 2 circleMeasure := by
  exact (memLp_top_of_bound hB 1 hbound).mono_exponent (by simp)

lemma matrixPoisson_boundary_memLp {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure) :
    MemLp (fun t => B t+Complex.I • matrixHilbert B t) 2 circleMeasure :=
  hB.add ((matrixHilbert_memLp_operator B).const_smul Complex.I)

lemma matrixPoisson_boundary_realPart {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian) :
    ∀ᵐ t ∂circleMeasure, hermitianRealPart (B t+Complex.I • matrixHilbert B t)=B t := by
  have hHB := matrixHilbert_hermitian_of_entries B (matrix_memLp_entries hB) hherm
  filter_upwards [hherm,hHB] with t ht hHt
  exact hermitianRealPart_add_I_smul ht hHt

lemma matrixPoisson_boundary_mem_closed_strip {r : ℕ} {B : UnitCircle → Circulation.Mat r}
    (hB : MemLp B 2 circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1) :
    ∀ᵐ t ∂circleMeasure,
      ‖hermitianRealPart (B t+Complex.I • matrixHilbert B t)‖ ≤ 1 := by
  filter_upwards [matrixPoisson_boundary_realPart hB hherm,hbound] with t ht hb
  rwa [ht]

lemma matrixPoissonRadial_mem_closed_strip {r : ℕ}
    (B : UnitCircle → Circulation.Mat r) (hB : AEStronglyMeasurable B circleMeasure)
    (hherm : ∀ᵐ t ∂circleMeasure, (B t).IsHermitian)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖B t‖ ≤ 1)
    (hmean : (∫ t, B t ∂circleMeasure)=0)
    {ρ : ℝ} (hρ : ρ ∈ Ico (0 : ℝ) 1) (t : UnitCircle) :
    ‖hermitianRealPart (matrixPoissonRadial B ρ t)‖ ≤ 1 := by
  have hn : ‖(ρ : ℂ)*fourier 1 t‖=ρ := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hρ.1,
      circle_fourier_norm,mul_one]
  have h := matrixPoissonAnalytic_realPart_norm B hB hherm hbound hmean
    (z := (ρ : ℂ)*fourier 1 t) (by rw [hn]; exact hρ.2)
  rw [hn] at h
  exact h.trans (by
    apply (div_le_iff₀ (by linarith [hρ.1] : 0 < 1+ρ)).mpr
    linarith [hρ.2])

end Operator
end
end CGLMPBounds.Hardy
