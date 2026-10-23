module

public import CGLMPBounds.Partition.ScalarCutFourier
public import CGLMPBounds.Circulation.Core

@[expose] public section


/-! Scalar branches in the actual normalized matrix Fourier energy. These
identities prove the scalar-cut baseline without replacing the matrix norm
by an unnormalized surrogate. -/

namespace CGLMPBounds.Partition
open MeasureTheory
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section

lemma hsSq_complex_smul {r : ℕ} (z : ℂ) (M : Circulation.Mat r) :
    Circulation.hsSq (z • M) = ‖z‖ ^ 2 * Circulation.hsSq M := by
  simp only [Circulation.hsSq, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Complex.star_def, Complex.mul_conj',
    ← Complex.ofReal_pow, Circulation.reTr_smul]

lemma hsSq_unitary {r : ℕ} (hr : 0 < r) (W : Circulation.Mat r)
    (hW : Wᴴ * W = 1) : Circulation.hsSq W = 1 := by
  rw [Circulation.hsSq, hW, Circulation.reTr_eq]
  simp [Nat.ne_of_gt hr]

lemma matrixNegativeFourierCoefficient_scalar_smul {r : ℕ}
    (f : ℝ → ℂ) (W : Circulation.Mat r) (n : ℕ) :
    matrixNegativeFourierCoefficient (fun t => f t • W) n =
      (∫ t in (0 : ℝ)..1,
        Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          f t) • W := by
  letI : ENormedAddMonoid (Circulation.Mat r) :=
    inferInstanceAs (ENormedAddMonoid (Fin r → Fin r → ℂ))
  unfold matrixNegativeFourierCoefficient
  simp_rw [smul_smul]
  exact intervalIntegral.integral_smul_const _ _

lemma matrixNegativeFourierEnergy_scalar_smul {r : ℕ}
    (f : ℝ → ℂ) (W : Circulation.Mat r) :
    matrixNegativeFourierEnergy (fun t => f t • W) =
      (∑' n : ℕ, ‖∫ t in (0 : ℝ)..1,
        Complex.exp (((2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          f t‖ ^ 2) * Circulation.hsSq W := by
  unfold matrixNegativeFourierEnergy
  simp_rw [matrixNegativeFourierCoefficient_scalar_smul, hsSq_complex_smul]
  exact tsum_mul_right

/-- Every matrix scalar cut has the same normalized negative energy ν₄. -/
theorem sourceScalarCutBranch_matrix_negative_energy {r : ℕ} (hr : 0 < r)
    (W : Circulation.Mat r) (hW : Wᴴ * W = 1) (a : ℤ) (T : ℝ)
    (hT : T ∈ Set.Icc (0 : ℝ) 1) :
    matrixNegativeFourierEnergy (fun t => sourceScalarCutBranch a T t • W) =
      sourceFourthRootHardyConstant := by
  rw [matrixNegativeFourierEnergy_scalar_smul,
    sourceScalarCutBranch_negative_energy a T hT, hsSq_unitary hr W hW, mul_one]

end
end CGLMPBounds.Partition
