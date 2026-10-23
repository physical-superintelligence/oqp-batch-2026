module

public import ThreeCopyQutritWerner.CertificateX2Reduced

@[expose] public section


/-!
# The standard-kind partner

For a standard-kind h key the image `J` spans the half of the standard component that is even
under the swap of the first two slots; the odd half is spanned by the partner
`W = (P₁₂ - P₀₂) J`. If the form `f` commutes with the slot transpositions `P₁₂`, `P₀₂`
(involutions, self-adjoint) and `J + P₁₂ J + P₀₂ J = 0` (no trivial component, even under
`P₀₁`), then `Wᴴ f W = 3 Jᴴ f J`; the same with the metric gives `det (Wᴴ G W) ≠ 0` from
`det (Jᴴ G J) ≠ 0`. This is the odd standard part of `x2_posSemidef_of_parts_complex`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem x2_partner_sq {n r : Type*} [Fintype n] [DecidableEq n]
    (P12 P02 : Matrix n n ℂ) (J : Matrix n r ℂ)
    (h12 : P12 * P12 = 1) (h02 : P02 * P02 = 1) (hJ : J + P12 * J + P02 * J = 0) :
    (P12 - P02) * ((P12 - P02) * J) = (3 : ℂ) • J := by
  have hP02J : P02 * J = -J - P12 * J := by
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← hJ]
    abel
  have hP12J : P12 * J = -J - P02 * J := by
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← hJ]
    abel
  have e1 : P12 * (P02 * J) = -(P12 * J) - J := by
    rw [hP02J, Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc, h12, Matrix.one_mul]
  have e2 : P02 * (P12 * J) = -(P02 * J) - J := by
    rw [hP12J, Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc, h02, Matrix.one_mul]
  have e3 : P12 * (P12 * J) = J := by rw [← Matrix.mul_assoc, h12, Matrix.one_mul]
  have e4 : P02 * (P02 * J) = J := by rw [← Matrix.mul_assoc, h02, Matrix.one_mul]
  have hsum : P12 * J + P02 * J = -J := by
    rw [eq_neg_iff_add_eq_zero, ← hJ]
    abel
  calc (P12 - P02) * ((P12 - P02) * J)
      = P12 * (P12 * J) - P02 * (P12 * J) - (P12 * (P02 * J) - P02 * (P02 * J)) := by
        rw [Matrix.sub_mul P12 P02 J, Matrix.mul_sub (P12 - P02), Matrix.sub_mul, Matrix.sub_mul]
    _ = J - (-(P02 * J) - J) - ((-(P12 * J) - J) - J) := by rw [e3, e2, e1, e4]
    _ = (4 : ℂ) • J + (P12 * J + P02 * J) := by
        rw [show (4 : ℂ) • J = J + J + J + J by
          rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]]
        abel
    _ = (3 : ℂ) • J := by
        rw [hsum, show (4 : ℂ) • J = (3 : ℂ) • J + J by
          rw [show (4 : ℂ) = 3 + 1 by norm_num, add_smul, one_smul]]
        abel

/-- THE PARTNER FORM: `Wᴴ f W = 3 Jᴴ f J` for `W = (P₁₂ - P₀₂) J`. -/
theorem x2_partner_form {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
    (f P12 P02 : Matrix n n ℂ) (J : Matrix n r ℂ)
    (h12 : P12 * P12 = 1) (h02 : P02 * P02 = 1) (h12t : P12ᴴ = P12) (h02t : P02ᴴ = P02)
    (hf12 : f * P12 = P12 * f) (hf02 : f * P02 = P02 * f)
    (hJ : J + P12 * J + P02 * J = 0) :
    ((P12 - P02) * J)ᴴ * f * ((P12 - P02) * J) = (3 : ℂ) • (Jᴴ * f * J) := by
  have hcomm : (P12 - P02) * f = f * (P12 - P02) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hf12, hf02]
  have hadj : (P12 - P02)ᴴ = P12 - P02 := by
    rw [Matrix.conjTranspose_sub, h12t, h02t]
  rw [Matrix.conjTranspose_mul, hadj]
  calc Jᴴ * (P12 - P02) * f * ((P12 - P02) * J)
      = Jᴴ * ((P12 - P02) * f) * ((P12 - P02) * J) := by simp only [Matrix.mul_assoc]
    _ = Jᴴ * (f * (P12 - P02)) * ((P12 - P02) * J) := by rw [hcomm]
    _ = Jᴴ * f * ((P12 - P02) * ((P12 - P02) * J)) := by simp only [Matrix.mul_assoc]
    _ = Jᴴ * f * ((3 : ℂ) • J) := by rw [x2_partner_sq P12 P02 J h12 h02 hJ]
    _ = (3 : ℂ) • (Jᴴ * f * J) := by rw [Matrix.mul_smul]

/-- The two parts of a self-adjoint involution `S` (two equal slots): `P k = (1 ± S) / 2`. -/
def x2InvolutionPart {n : Type*} [Fintype n] [DecidableEq n] (S : Matrix n n ℂ) (k : Bool) :
    Matrix n n ℂ :=
  (1 / 2 : ℂ) • (1 + (if k then (-1 : ℂ) else 1) • S)

theorem x2InvolutionPart_sum {n : Type*} [Fintype n] [DecidableEq n] (S : Matrix n n ℂ) :
    ∑ k, x2InvolutionPart S k = 1 := by
  ext i j
  simp [Fintype.sum_bool, x2InvolutionPart, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply]
  try ring

theorem x2InvolutionPart_mul {n : Type*} [Fintype n] [DecidableEq n] (S : Matrix n n ℂ)
    (hS : S * S = 1) (k l : Bool) :
    x2InvolutionPart S k * x2InvolutionPart S l = if k = l then x2InvolutionPart S k else 0 := by
  have hsq : ∀ c d : ℂ, (1 + c • S) * (1 + d • S) = (1 + c * d) • 1 + (c + d) • S := by
    intro c d
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hS]
    module
  unfold x2InvolutionPart
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq]
  cases k <;> cases l <;>
    (ext i j; by_cases hij : i = j <;>
      simp [hij, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply] <;> ring)

theorem x2InvolutionPart_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℂ) (hSt : Sᴴ = S) (k : Bool) :
    (x2InvolutionPart S k)ᴴ = x2InvolutionPart S k := by
  unfold x2InvolutionPart
  cases k <;> simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hSt]

theorem x2InvolutionPart_comm {n : Type*} [Fintype n] [DecidableEq n] (S X : Matrix n n ℂ)
    (hX : X * S = S * X) (k : Bool) :
    X * x2InvolutionPart S k = x2InvolutionPart S k * X := by
  unfold x2InvolutionPart
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, hX, Matrix.mul_one, Matrix.one_mul]

end ThreeCopyQutritWerner

end
