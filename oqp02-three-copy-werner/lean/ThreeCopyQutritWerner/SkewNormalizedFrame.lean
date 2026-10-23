module

public import ThreeCopyQutritWerner.SkewRankTwoNormal

@[expose] public section


/-!
# Normalized rank-two skew matrices in the manuscript's exact convention

A unit phase is absorbed into one orthonormal column. Thus the coefficient is
exactly 1/sqrt(2), including its sign and phase, without adding an overall-phase
hypothesis to the family definition.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Unit Frobenius norm fixes the scalar coefficient; its phase can be included
in one of the two orthonormal columns. -/
theorem exists_unit_skew_frame {n : Type*} [Fintype n]
    (K : Matrix n n ℂ) (hK : Kᵀ = -K) (hr : K.rank = 2) (hN : frobSq K = 1) :
    ∃ U : Matrix n (Fin 2) ℂ, Uᴴ * U = 1 ∧
      K = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ) := by
  classical
  obtain ⟨U, z, hU, hKz, hz⟩ := exists_normalized_orthonormal_skew_factor K hK hr
  rw [hN] at hz
  let w : ℂ := (Real.sqrt 2 : ℂ) * z
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    simpa only [pow_two] using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hsne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  have hw : Complex.normSq w = 1 := by
    dsimp [w]
    rw [Complex.normSq_mul, Complex.normSq_ofReal, hs]
    exact hz
  let T : Matrix (Fin 2) (Fin 2) ℂ := !![w, 0; 0, 1]
  have hT : Tᴴ * T = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hw]
  have hTeps : T * epsMat * Tᵀ = w • epsMat := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, epsMat, Matrix.mul_apply, Fin.sum_univ_two]
  let W := U * T
  have hW : Wᴴ * W = 1 := by
    dsimp [W]
    calc
      (U * T)ᴴ * (U * T) = Tᴴ * (Uᴴ * U) * T := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hT]
  have hWeps : W * epsMat * Wᵀ = w • (U * epsMat * Uᵀ) := by
    dsimp [W]
    calc
      U * T * epsMat * (U * T)ᵀ = U * (T * epsMat * Tᵀ) * Uᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTeps, Matrix.mul_smul, Matrix.smul_mul]
  have hwz : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * w = z := by
    dsimp [w]
    rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hsne, one_mul]
  refine ⟨W, hW, ?_⟩
  rw [hWeps, smul_smul, hwz]
  exact hKz

/-- A normalized rank-two two-qubit operator with skew spin transform is `binaryB₂ U` for an
isometry `U` (the two-qubit factor of family II of Theorem 5.1), including the prescribed
normalization. -/
theorem exists_binaryB₂_of_skew_spin
    (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hr : C.rank = 2) (hN : frobSq C = 1)
    (hskew : (C * epsJ₂)ᵀ = -(C * epsJ₂)) :
    ∃ U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ, Uᴴ * U = 1 ∧ C = binaryB₂ U := by
  have hJ : epsJ₂ * epsJ₂ᴴ = 1 := by
    rw [epsJ₂, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      epsMat_mul_conjTranspose, Matrix.one_kronecker_one]
  have hrJ : (C * epsJ₂).rank = 2 := by
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans_eq hr
    · calc
        2 = C.rank := hr.symm
        _ = (C * epsJ₂ * epsJ₂ᴴ).rank := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
        _ ≤ (C * epsJ₂).rank := Matrix.rank_mul_le_left _ _
  obtain ⟨U, hU, hK⟩ := exists_unit_skew_frame (C * epsJ₂) hskew hrJ
    ((frobSq_mul_unitary C epsJ₂ hJ).trans hN)
  refine ⟨U, hU, ?_⟩
  have h := congrArg (fun M => M * epsJ₂ᵀ) hK
  have hJJt : epsJ₂ * epsJ₂ᵀ = 1 :=
    mul_eq_one_comm.mp epsJ₂_transpose_mul_self
  rw [Matrix.mul_assoc, hJJt, Matrix.mul_one, Matrix.smul_mul] at h
  simpa only [binaryB₂, epsJ₂_inv] using h

/-- The identical normalization statement for the three-qubit binary carrier. -/
theorem exists_binaryB₃_of_skew_spin
    (C : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hr : C.rank = 2) (hN : frobSq C = 1)
    (hskew : (C * epsJ₃)ᵀ = -(C * epsJ₃)) :
    ∃ U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ,
      Uᴴ * U = 1 ∧ C = binaryB₃ U := by
  have hJ : epsJ₃ * epsJ₃ᴴ = 1 := by
    rw [epsJ₃, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      epsMat_mul_conjTranspose, Matrix.one_kronecker_one, Matrix.one_kronecker_one]
  have hrJ : (C * epsJ₃).rank = 2 := by
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans_eq hr
    · calc
        2 = C.rank := hr.symm
        _ = (C * epsJ₃ * epsJ₃ᴴ).rank := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
        _ ≤ (C * epsJ₃).rank := Matrix.rank_mul_le_left _ _
  obtain ⟨U, hU, hK⟩ := exists_unit_skew_frame (C * epsJ₃) hskew hrJ
    ((frobSq_mul_unitary C epsJ₃ hJ).trans hN)
  refine ⟨U, hU, ?_⟩
  have h := congrArg (fun M => M * epsJ₃ᵀ) hK
  have hJJt : epsJ₃ * epsJ₃ᵀ = 1 :=
    mul_eq_one_comm.mp epsJ₃_transpose_mul_self
  rw [Matrix.mul_assoc, hJJt, Matrix.mul_one, Matrix.smul_mul] at h
  simpa only [binaryB₃, epsJ₃_inv] using h

end ThreeCopyQutritWerner
