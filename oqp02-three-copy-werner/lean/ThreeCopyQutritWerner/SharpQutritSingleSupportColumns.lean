module

public import ThreeCopyQutritWerner.SharpQutritSingleSupport

@[expose] public section


/-!
# Two-sided physical support of normal sharp extremizers

Ordinary transpose leaves the double-antisymmetric projection unchanged.
The same actual saturation argument therefore gives column support, with
the identical missing coordinate and without a conjugation change.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Swapping the entire two-replica coefficient matrix does not change Q. -/
theorem sharpDoubleAnti_of_transpose {L R : Type*}
    (X : Matrix (L × R) (L × R) ℂ) : sharpDoubleAnti Xᵀ = sharpDoubleAnti X := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [sharpDoubleAnti, sharpSwapLeft, sharpSwapRight, Matrix.transpose_apply]
  ring

/-- A single exterior coefficient also excludes its missing coordinate from
both local column registers of the original matrix. -/
theorem sharpQutritDiagonal_saturation_single_columns_zero
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y)
    (a : Fin 3) (ha : ∀ b, b ≠ a → d b = 0)
    (i j : Fin 3) (p : Fin 3 × Fin 3) (hij : i = a ∨ j = a) : Y p (i, j) = 0 := by
  have hr : Yᵀ.rank ≤ 2 := by rwa [Matrix.rank_transpose]
  have hQt : sharpDoubleAnti Yᵀ =
      sharpQutritAntiEncode (Matrix.diagonal (fun b => (d b : ℂ))) := by
    rwa [sharpDoubleAnti_of_transpose]
  have hst : frobSq (sharpDoubleAnti Yᵀ) = frobSq Yᵀ / 2 := by
    rwa [sharpDoubleAnti_of_transpose, frobSq_transpose']
  have hpt : 0 < frobSq Yᵀ := by rwa [frobSq_transpose']
  exact sharpQutritDiagonal_saturation_single_rows_zero d hd Yᵀ hr hQt hst hpt a ha i j p hij

/-- A nonnegative diagonal sharp extremizer with singular actual range has
one fixed missing coordinate on both local registers, in rows and columns. -/
theorem sharpQutritDiagonal_saturation_exists_support_coordinate
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i)
    (Y : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) (hY : Y.rank ≤ 2)
    (hQ : sharpDoubleAnti Y = sharpQutritAntiEncode (Matrix.diagonal (fun i => (d i : ℂ))))
    (hs : frobSq (sharpDoubleAnti Y) = frobSq Y / 2) (hpos : 0 < frobSq Y)
    (hrange : ∀ v : Fin 3 × Fin 3 → ℂ, (sharpReshape (Y *ᵥ v)).det = 0) :
    ∃ a : Fin 3, ∀ i j p, i = a ∨ j = a → Y (i, j) p = 0 ∧ Y p (i, j) = 0 := by
  have hc := sharpQutritDiagonal_saturation_singular_range_single_coefficient
    d hd Y hY hQ hs hpos hrange
  have ha : ∃ a : Fin 3, ∀ b, b ≠ a → d b = 0 := by
    rcases hc with hc | hc | hc
    · refine ⟨0, ?_⟩
      intro b hb
      fin_cases b
      · exact (hb rfl).elim
      · exact hc.1
      · exact hc.2
    · refine ⟨1, ?_⟩
      intro b hb
      fin_cases b
      · exact hc.1
      · exact (hb rfl).elim
      · exact hc.2
    · refine ⟨2, ?_⟩
      intro b hb
      fin_cases b
      · exact hc.1
      · exact hc.2
      · exact (hb rfl).elim
  obtain ⟨a, ha⟩ := ha
  refine ⟨a, ?_⟩
  intro i j p hij
  exact ⟨sharpQutritDiagonal_saturation_single_rows_zero d hd Y hY hQ hs hpos a ha i j p hij,
    sharpQutritDiagonal_saturation_single_columns_zero d hd Y hY hQ hs hpos a ha i j p hij⟩

end ThreeCopyQutritWerner
