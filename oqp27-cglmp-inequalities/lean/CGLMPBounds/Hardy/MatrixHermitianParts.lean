module

public import CGLMPBounds.Defs.CircularHilbert
public import CGLMPBounds.Hardy.HolomorphicPinchingRectangle

@[expose] public section


/-! Actual Hermitian real and imaginary matrix parts and their numerical
range bounds. No normality or simultaneous diagonalization is needed. -/
namespace CGLMPBounds.Hardy
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

lemma hermitianRealPart_isHermitian {r : ℕ} (X : Circulation.Mat r) :
    (hermitianRealPart X).IsHermitian := by
  change (hermitianRealPart X)ᴴ = hermitianRealPart X
  simp only [hermitianRealPart, conjTranspose_smul, conjTranspose_add,
    conjTranspose_conjTranspose]
  simp [add_comm]

lemma hermitianImagPart_isHermitian {r : ℕ} (X : Circulation.Mat r) :
    (hermitianImagPart X).IsHermitian := by
  change (hermitianImagPart X)ᴴ = hermitianImagPart X
  simp only [hermitianImagPart, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_conjTranspose]
  simp only [star_div₀, star_neg, star_ofNat, Complex.star_def, Complex.conj_I]
  module

lemma hermitianParts_reconstruct {r : ℕ} (X : Circulation.Mat r) :
    hermitianRealPart X + Complex.I • hermitianImagPart X = X := by
  simp only [hermitianRealPart, hermitianImagPart, smul_smul]
  have hi : Complex.I * (-Complex.I / 2) = (1/2 : ℂ) := by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
    norm_num
  rw [hi]
  module

lemma hermitianRealPart_add_I_smul {r : ℕ} {H Y : Circulation.Mat r}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) :
    hermitianRealPart (H+Complex.I • Y) = H := by
  simp only [hermitianRealPart, conjTranspose_add, conjTranspose_smul,
    Complex.star_def, Complex.conj_I, hH.eq, hY.eq]
  module

lemma hermitianImagPart_add_I_smul {r : ℕ} {H Y : Circulation.Mat r}
    (hH : H.IsHermitian) (hY : Y.IsHermitian) :
    hermitianImagPart (H+Complex.I • Y) = Y := by
  simp only [hermitianImagPart, conjTranspose_add, conjTranspose_smul,
    Complex.star_def, Complex.conj_I, hH.eq, hY.eq]
  have hi : (-Complex.I/2) * (2*Complex.I) = (1 : ℂ) := by
    field_simp
    simp [Complex.I_mul_I]
  calc
    _ = ((-Complex.I/2)*(2*Complex.I)) • Y := by module
    _ = Y := by rw [hi, one_smul]

lemma matrix_spectrum_parts_rectangle {r : ℕ} (X : Circulation.Mat r)
    {z : ℂ} (hz : z ∈ spectrum ℂ X) :
    |z.re| ≤ ‖hermitianRealPart X‖ ∧ |z.im| ≤ ‖hermitianImagPart X‖ := by
  apply matrix_spectrum_real_imaginary_rectangle
    (hermitianRealPart_isHermitian X) (hermitianImagPart_isHermitian X)
  simpa only [hermitianParts_reconstruct] using hz

end
end CGLMPBounds.Hardy
