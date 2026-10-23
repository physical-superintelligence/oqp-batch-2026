module

public import ThreeCopyQutritWerner.TwoCutPolarizedSupport
public import ThreeCopyQutritWerner.SingularUnitaryCompletion

@[expose] public section


/-!
# Actual rank-two anchors for polarized-null qutrit pairs

An actual singular-value decomposition supplies the diagonal anchor. Thus a
rank-two matrix and any polarized-null partner have simultaneous missing rows
and columns after actual local unitary coordinate changes. These coordinates
describe this pair; they do not align the output and input planes of an operator.
-/

noncomputable section

open scoped Matrix

namespace ThreeCopyQutritWerner

/-- A qutrit diagonal of actual rank two has exactly one missing coordinate. -/
theorem sharpQutrit_rank_diagonal_two_missing (d : Fin 3 → ℂ)
    (h : (Matrix.diagonal d).rank = 2) :
    ∃ a : Fin 3, d a = 0 ∧ ∀ j, j ≠ a → d j ≠ 0 := by
  classical
  rw [Matrix.rank_diagonal] at h
  simp only [Fintype.card_subtype] at h
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [huniv] at h
  by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0 <;> by_cases h2 : d 2 = 0
  all_goals norm_num [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2] at h
  all_goals first
    | exact ⟨0, h0, by intro j hj; fin_cases j <;> simp_all⟩
    | exact ⟨1, h1, by intro j hj; fin_cases j <;> simp_all⟩
    | exact ⟨2, h2, by intro j hj; fin_cases j <;> simp_all⟩

/-- A literal rank-two polarized-null anchor gives simultaneous local planes
for both original matrices, through constructed unitary coordinates. -/
theorem sharpPolarizedMinor_rank_two_exists_missing_coordinates
    (A B : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.rank = 2)
    (h : ∀ i j k l, sharpPolarizedMinor A B i j k l = 0) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ i, (U * A * V) a i = 0 ∧ (U * A * V) i a = 0 ∧
        (U * B * V) a i = 0 ∧ (U * B * V) i a = 0 := by
  obtain ⟨L, R, d, hL, hR, hd, he⟩ := singularFamily_exists_unitary_diagonalization A
  have hLL : L * Lᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hL
  have hRR : R * Rᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hR
  have hrec : L * Matrix.diagonal (fun i => (d i : ℂ)) * Rᴴ = A := by
    rw [← he]
    calc
      L * (Lᴴ * A * R) * Rᴴ = (L * Lᴴ) * A * (R * Rᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hLL, hRR, Matrix.one_mul, Matrix.mul_one]
  have hr : (Matrix.diagonal (fun i => (d i : ℂ))).rank = 2 := by
    apply le_antisymm
    · rw [← he]
      exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans_eq hA
    · calc
        2 = A.rank := hA.symm
        _ = (L * Matrix.diagonal (fun i => (d i : ℂ)) * Rᴴ).rank :=
          congrArg Matrix.rank hrec.symm
        _ ≤ (Matrix.diagonal (fun i => (d i : ℂ))).rank :=
          (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  obtain ⟨a, ha, hda⟩ := sharpQutrit_rank_diagonal_two_missing _ hr
  have hp : ∀ i j k l, sharpPolarizedMinor
      (Matrix.diagonal (fun i => (d i : ℂ))) (Lᴴ * B * R) i j k l = 0 := by
    rw [← he]
    exact sharpPolarizedMinor_two_sided_null Lᴴ R A B h
  have hb := sharpPolarizedMinor_diagonal_missing_coordinate _ a ha hda (Lᴴ * B * R) hp
  refine ⟨Lᴴ, R, a, ?_, hR, ?_⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using hLL
  · intro i
    refine ⟨?_, ?_, (hb i).1, (hb i).2⟩
    · rw [he]
      simp [Matrix.diagonal_apply, ha]
    · rw [he]
      by_cases hi : i = a
      · subst i
        simpa only [Matrix.diagonal_apply_eq] using ha
      · simp [Matrix.diagonal_apply, hi]

end ThreeCopyQutritWerner
