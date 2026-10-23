module

public import ThreeCopyQutritWerner.TwoCutFixedRowPlane

@[expose] public section


/-! Exact coefficient extraction for the original fixed-row source pencil. -/

noncomputable section

open scoped Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

theorem exists_two_distinct_nonzero_affine_rays
    {a : Type*} (u v : a → ℂ) (hn : u ≠ 0 ∨ v ≠ 0) :
    ∃ z w : ℂ, z ≠ w ∧ u + z • v ≠ 0 ∧ u + w • v ≠ 0 := by
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hn.resolve_left (not_not.mpr hu)
    exact ⟨1, -1, by norm_num, by simpa [hu] using hv, by simpa [hu] using hv⟩
  by_cases hp : u + v = 0
  · refine ⟨0, -1, by norm_num, by simpa using hu, ?_⟩
    intro hm
    apply hu
    ext i
    have h1 := congrFun hp i
    have h2 := congrFun hm i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
    linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2
  · exact ⟨0, 1, by norm_num, by simpa using hu, by simpa using hp⟩

theorem fixedRow_partner_pencil_block
    (R : Matrix (Fin 3) (Fin 2) ℂ)
    (A B D : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ) (z t : ℂ) (j : Fin 3) :
    R * (firstSiteFactorBlock (B - conj z • A + t • D) j)ᴴ =
      R * (firstSiteFactorBlock B j)ᴴ - z • (R * (firstSiteFactorBlock A j)ᴴ) +
        conj t • (R * (firstSiteFactorBlock D j)ᴴ) := by
  have he : firstSiteFactorBlock (B - conj z • A + t • D) j =
      firstSiteFactorBlock B j - conj z • firstSiteFactorBlock A j +
        t • firstSiteFactorBlock D j := rfl
  rw [he]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_conj,
    Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul]

theorem matrix_affine_projection_coefficients
    {m n : Type*} (A B D P : Matrix m n ℂ) (z w α β γ : ℂ) (hzw : z ≠ w)
    (h0 : B - z • A = α • P) (h1 : B - w • A = β • P)
    (h2 : B - z • A + D = γ • P) :
    ∃ a b d : ℂ, A = a • P ∧ B = b • P ∧ D = d • P := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzw)
  let a := (α - β) / (w - z)
  have ha : A = a • P := by
    ext i j
    have e0 := congrFun (congrFun h0 i) j
    have e1 := congrFun (congrFun h1 i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e0 e1 ⊢
    dsimp only [a]
    rw [div_mul_eq_mul_div₀]
    apply (eq_div_iff hwz).mpr
    linear_combination e0 - e1
  refine ⟨a, α + z * a, γ - α, ha, ?_, ?_⟩
  · ext i j
    have e0 := congrFun (congrFun h0 i) j
    rw [ha] at e0
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e0 ⊢
    linear_combination e0
  · ext i j
    have e0 := congrFun (congrFun h0 i) j
    have e2 := congrFun (congrFun h2 i) j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e0 e2 ⊢
    linear_combination e2 - e0

end ThreeCopyQutritWerner
