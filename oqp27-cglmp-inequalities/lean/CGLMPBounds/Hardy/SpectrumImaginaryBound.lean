module

public import Mathlib

@[expose] public section


/-! A finite-dimensional spectral bound in the Hilbert operator norm. If a
matrix is a Hermitian matrix plus E, the imaginary part of every eigenvalue is
bounded by ‖E‖. The matrix need not be normal or diagonalizable. -/

namespace CGLMPBounds.Hardy
noncomputable section
open scoped InnerProductSpace Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem clm_spectrum_abs_im_le_norm_perturbation
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] [CompleteSpace F]
    {K E : F →L[ℂ] F} (hK : IsSelfAdjoint K) {z : ℂ}
    (hz : z ∈ spectrum ℂ (K + E)) : |z.im| ≤ ‖E‖ := by
  have he : Module.End.HasEigenvalue ((K + E : F →L[ℂ] F) : F →ₗ[ℂ] F) z := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rwa [← ContinuousLinearMap.spectrum_eq]
  obtain ⟨w, hw⟩ := he.exists_hasEigenvector
  have hw0 : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw.2)
  have heq : K w + E w = z • w := hw.apply_eq_smul
  have hi := congrArg Complex.im
    (congrArg (fun v : F => inner ℂ w v) heq)
  have hk : (inner ℂ w (K w)).im = 0 := hK.isSymmetric.im_inner_self_apply w
  have hself : inner ℂ w w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa only [Complex.ofReal_re, RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) w)
    · simpa only [Complex.ofReal_im, RCLike.im_eq_complex_im] using (inner_self_im (𝕜 := ℂ) w)
  have hie : (inner ℂ w (E w)).im = z.im * ‖w‖ ^ 2 := by
    simpa only [inner_add_right,inner_smul_right,hself,Complex.add_im,hk,
      zero_add,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,add_zero] using hi
  have hbound : |(inner ℂ w (E w)).im| ≤ ‖E‖ * ‖w‖ ^ 2 := by
    calc
      |(inner ℂ w (E w)).im| ≤ ‖inner ℂ w (E w)‖ := Complex.abs_im_le_norm _
      _ ≤ ‖w‖ * ‖E w‖ := norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (‖E‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (E.le_opNorm w) (norm_nonneg w)
      _ = ‖E‖ * ‖w‖ ^ 2 := by ring
  rw [hie, abs_mul, abs_of_nonneg (sq_nonneg ‖w‖)] at hbound
  exact (mul_le_mul_iff_of_pos_right hw0).mp hbound

theorem matrix_spectrum_abs_im_le_norm_perturbation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K E : Matrix ι ι ℂ} (hK : K.IsHermitian) {z : ℂ}
    (hz : z ∈ spectrum ℂ (K + E)) : |z.im| ≤ ‖E‖ := by
  have hk : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) K) :=
    (show IsSelfAdjoint K from hK).map (Matrix.toEuclideanCLM (𝕜 := ℂ))
  have hspec : z ∈ spectrum ℂ
      (Matrix.toEuclideanCLM (𝕜 := ℂ) K + Matrix.toEuclideanCLM (𝕜 := ℂ) E) := by
    rw [← map_add, AlgEquiv.spectrum_eq]
    exact hz
  simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
    clm_spectrum_abs_im_le_norm_perturbation hk hspec

end
end CGLMPBounds.Hardy
