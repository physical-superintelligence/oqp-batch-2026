module

public import ThreeCopyQutritWerner.ZeroRelationsAlgebra
public import ThreeCopyQutritWerner.TwoPlane
public import Mathlib.Analysis.RCLike.Sqrt

@[expose] public section


/-!
# Appendix C: algebra for the rank-two symmetric feature

If `H(C,p)` has rank two, its range equals the rank-two range of `C`; an explicit factor
`C=H M` witnesses the missing inclusion. A complex symmetric binary quadratic splits into a
symmetrized product, giving `H=x yᵀ+y xᵀ` with nonproportional `x,y` when `rank H=2`.
The further local-support consequence of the vanishing mixed minors is separate.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- When the symmetric feature has rank two, `ran C ⊆ ran H` has an explicit right factor.
Together with `hFeature_eq_mul_left_of_rank_two`, this gives equality of the two ranges. -/
theorem eq_hFeature_mul_of_rank_two {n : Type*} [Fintype n]
    (X : Matrix n (Fin 2) ℂ) (B : Matrix (Fin 2) n ℂ)
    (hH : (hFeature (X * B) (bivecMat X)).rank = 2) :
    ∃ M : Matrix n n ℂ, X * B = hFeature (X * B) (bivecMat X) * M := by
  let K : Matrix (Fin 2) n ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    ((B * X - ((X * B).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * epsMat * Xᵀ)
  have hHK : hFeature (X * B) (bivecMat X) = X * K := hFeature_eq_mul X B
  obtain ⟨R, hR⟩ := exists_right_inverse_of_rank_eq_two K
    (rank_eq_two_of_mul X K (hHK ▸ hH)).2
  refine ⟨R * B, ?_⟩
  rw [hHK]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc K R, hR, Matrix.one_mul]

/-- Every complex symmetric binary quadratic splits as a symmetrized product of two
linear forms. This includes degenerate quadratics. -/
theorem exists_symmetrized_factor_two (D : Matrix (Fin 2) (Fin 2) ℂ) (hD : Dᵀ = D) :
    ∃ u v : Fin 2 → ℂ, ∀ i j, D i j = u i * v j + v i * u j := by
  have h10 : D 1 0 = D 0 1 := by
    exact congrFun (congrFun hD 0) 1
  by_cases ha : D 0 0 = 0
  · refine ⟨![D 0 1, D 1 1 / 2], ![0, 1], ?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · change D 0 0 = D 0 1 * 0 + 0 * D 0 1
      rw [ha]
      ring
    · change D 0 1 = D 0 1 * 1 + 0 * (D 1 1 / 2)
      ring
    · change D 1 0 = D 1 1 / 2 * 0 + 1 * D 0 1
      rw [h10]
      ring
    · change D 1 1 = D 1 1 / 2 * 1 + 1 * (D 1 1 / 2)
      ring
  · let s : ℂ := Complex.sqrt ((D 0 1) ^ 2 - D 0 0 * D 1 1)
    have hs : s ^ 2 = (D 0 1) ^ 2 - D 0 0 * D 1 1 := by
      exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
    let t : ℂ := (D 0 1 + s) / D 0 0
    have hid : D 0 0 * (D 0 0 * t ^ 2 - 2 * D 0 1 * t + D 1 1) =
        s ^ 2 - ((D 0 1) ^ 2 - D 0 0 * D 1 1) := by
      dsimp [t]
      field_simp [ha] <;> ring
    have hroot : D 0 0 * t ^ 2 - 2 * D 0 1 * t + D 1 1 = 0 := by
      exact (mul_eq_zero.mp (show D 0 0 *
        (D 0 0 * t ^ 2 - 2 * D 0 1 * t + D 1 1) = 0 by rw [hid, hs, sub_self])).resolve_left ha
    refine ⟨![1, t], ![D 0 0 / 2, D 0 1 - D 0 0 * t / 2], ?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · change D 0 0 = 1 * (D 0 0 / 2) + D 0 0 / 2 * 1
      ring
    · change D 0 1 = 1 * (D 0 1 - D 0 0 * t / 2) + D 0 0 / 2 * t
      ring
    · change D 1 0 = t * (D 0 0 / 2) + (D 0 1 - D 0 0 * t / 2) * 1
      rw [h10]
      ring
    · change D 1 1 = t * (D 0 1 - D 0 0 * t / 2) + (D 0 1 - D 0 0 * t / 2) * t
      linear_combination hroot

/-- A symmetric matrix of rank two admits the off-diagonal factorization used in
Appendix C's mixed-minor argument. -/
theorem exists_symmetrized_factor_of_rank_two {n : Type*} [Fintype n]
    (H : Matrix n n ℂ) (hr : H.rank = 2) (hs : Hᵀ = H) :
    ∃ x y : n → ℂ, ∀ i j, H i j = x i * y j + y i * x j := by
  obtain ⟨X, B, hXB⟩ := (rank_le_iff_exists_mul H 2).mp hr.le
  obtain ⟨L, hL⟩ := exists_left_inverse_of_rank_eq_two X
    (rank_eq_two_of_mul X B (hXB ▸ hr)).1
  let D : Matrix (Fin 2) (Fin 2) ℂ := L * H * Lᵀ
  have hD : Dᵀ = D := by
    dsimp [D]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs,
      Matrix.mul_assoc]
  have hleft : X * L * H = H := by
    rw [hXB]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc L X, hL, Matrix.one_mul]
  have hright : H * Lᵀ * Xᵀ = H := by
    have h := congrArg Matrix.transpose hleft
    simpa only [Matrix.transpose_mul, hs, Matrix.mul_assoc] using h
  have hrep : H = X * D * Xᵀ := by
    dsimp [D]
    calc
      H = H * Lᵀ * Xᵀ := hright.symm
      _ = (X * L * H) * Lᵀ * Xᵀ := by rw [hleft]
      _ = X * (L * H * Lᵀ) * Xᵀ := by simp only [Matrix.mul_assoc]
  obtain ⟨u, v, huv⟩ := exists_symmetrized_factor_two D hD
  refine ⟨X *ᵥ u, X *ᵥ v, ?_⟩
  intro i j
  rw [hrep]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, huv]
  ring

/-- Rank two excludes proportional vectors in a symmetrized-product factorization. -/
theorem not_isMultiple_of_rank_two_symmetrized {n : Type*} [Fintype n]
    (H : Matrix n n ℂ) (hr : H.rank = 2) (x y : n → ℂ)
    (hf : ∀ i j, H i j = x i * y j + y i * x j) : ¬ TwoPlane.IsMultiple x y := by
  rintro ⟨z, hz⟩
  have hr1 : H.rank ≤ 1 := by
    apply (rank_le_iff_exists_mul H 1).mpr
    refine ⟨Matrix.of fun i (_ : Fin 1) => x i,
      Matrix.of fun (_ : Fin 1) j => (2 * z) * x j, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply, hf, hz]
    ring
  omega

end ThreeCopyQutritWerner

end
