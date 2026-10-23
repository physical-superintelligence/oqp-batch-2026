module

public import CGLMPBounds.Hardy.MatrixHermitianParts
public import CGLMPBounds.Circulation.Spectral

@[expose] public section


/-! The literal A=ReW+ImW and B=ReW−ImW are commuting Hermitian
involutions for every unitary fourth root W. -/

namespace CGLMPBounds.Hardy
open Matrix
noncomputable section

 theorem fourthRoot_hermitian_parts {r : ℕ} (X : Circulation.Mat r)
    (hunit : Xᴴ * X = 1) (hfour : X^4 = 1) :
    (hermitianRealPart X + hermitianImagPart X).IsHermitian ∧
    (hermitianRealPart X - hermitianImagPart X).IsHermitian ∧
    (hermitianRealPart X + hermitianImagPart X)^2 = 1 ∧
    (hermitianRealPart X - hermitianImagPart X)^2 = 1 ∧
    (hermitianRealPart X + hermitianImagPart X) *
        (hermitianRealPart X - hermitianImagPart X) =
      (hermitianRealPart X - hermitianImagPart X) *
        (hermitianRealPart X + hermitianImagPart X) := by
  have hright : X * Xᴴ = 1 := (Matrix.mul_eq_one_comm_of_card_eq (Fin r) (Fin r) ℂ rfl).mp hunit
  have hs := Circulation.fourth_root_star hunit hfour
  have hsquare : Xᴴ * Xᴴ = X*X := by
    rw [hs, ← pow_add]
    calc X^(3+3) = X^4 * X^2 := by rw [← pow_add]
      _ = X*X := by rw [hfour, one_mul, pow_two]
  have hsum : hermitianRealPart X * hermitianRealPart X +
      hermitianImagPart X * hermitianImagPart X = 1 := by
    simp only [hermitianRealPart, hermitianImagPart, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      hunit, hright, hsquare]
    match_scalars <;> ring_nf <;> norm_num [Complex.I_sq]
  have hRI : hermitianRealPart X * hermitianImagPart X = 0 := by
    simp only [hermitianRealPart, hermitianImagPart, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      hunit, hright, hsquare]
    module
  have hIR : hermitianImagPart X * hermitianRealPart X = 0 := by
    simp only [hermitianRealPart, hermitianImagPart, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      hunit, hright, hsquare]
    module
  refine ⟨(hermitianRealPart_isHermitian X).add (hermitianImagPart_isHermitian X),
    (hermitianRealPart_isHermitian X).sub (hermitianImagPart_isHermitian X), ?_, ?_, ?_⟩
  · simpa only [pow_two, Matrix.add_mul, Matrix.mul_add, hRI, hIR, zero_add, add_zero] using hsum
  · simpa only [pow_two, Matrix.sub_mul, Matrix.mul_sub, hRI, hIR, sub_zero, zero_sub,
      sub_neg_eq_add] using hsum
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      hRI, hIR, add_zero, zero_add, sub_zero, zero_sub]
    abel

end
end CGLMPBounds.Hardy
