module

public import ThreeCopyQutritWerner.TwoCutFixedRowProjection

@[expose] public section


/-! One constructed plane works for every actual fixed-row partner. -/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

theorem qutrit_twoColumn_exists_projection_fixing
    (R : Matrix (Fin 3) (Fin 2) ℂ) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℂ,
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧ P * R = R := by
  have hr : R.rank ≤ 2 := by simpa using Matrix.rank_le_card_width R
  obtain ⟨J, hJ, hfix⟩ := qutrit_rank_le_two_exists_binary_frame R hr
  refine ⟨J * Jᴴ, Matrix.isHermitian_mul_conjTranspose_self J, ?_, ?_, hfix⟩
  · calc
      (J * Jᴴ) * (J * Jᴴ) = J * (Jᴴ * J) * Jᴴ := by simp only [Matrix.mul_assoc]
      _ = J * Jᴴ := by rw [hJ, Matrix.mul_one]
  · simpa only [Matrix.mul_one, Matrix.rank_one, Fintype.card_fin] using
      productRay_rank_conj_isometry J hJ (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem fixed_row_exists_common_cut_projection
    (R : Matrix (Fin 3) (Fin 2) ℂ) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℂ,
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧ P * R = R ∧
      ∀ (u : Fin 3 → ℂ) (Y : Matrix (Fin 3 × Fin 3) (Fin 2) ℂ),
        u ≠ 0 → cutForm (twoSiteVectorSource u R * Yᴴ) = 0 →
          ∀ j : Fin 3, ∃ α : ℂ, R * (firstSiteFactorBlock Y j)ᴴ = α • P := by
  obtain ⟨P, hP, hPP, hPr, hPR⟩ := qutrit_twoColumn_exists_projection_fixing R
  exact ⟨P, hP, hPP, hPr, hPR, fun u Y hu hq =>
    cutForm_zero_fixed_row_projection_blocks P hP hPP hPr R hPR u hu Y hq⟩

end ThreeCopyQutritWerner
