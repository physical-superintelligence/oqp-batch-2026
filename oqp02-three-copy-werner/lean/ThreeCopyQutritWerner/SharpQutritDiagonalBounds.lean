module

public import ThreeCopyQutritWerner.SharpQutritDiagonalBasis
public import ThreeCopyQutritWerner.RankTwoSpectralBound

@[expose] public section


/-!
# Exact one- and two-weight bounds for the full physical diagonal form

All nine signed weights belong to the constructed original-coordinate basis.
The two actual central extremes dominate every external squared weight.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

theorem sharpQutritExternalWeight_sq (d : Fin 3 → ℝ) (a : Fin 3) (s : Fin 2) :
    sharpQutritExternalWeight d a s ^ 2 = d a ^ 2 := by
  unfold sharpQutritExternalWeight
  split_ifs <;> ring

theorem sharpQutritCentralOrdered_extreme_signs (d : Fin 3 → ℝ) :
    0 ≤ sharpQutritCentralOrdered d 0 ∧ sharpQutritCentralOrdered d 2 ≤ 0 := by
  have hs := sharpQutritCentralOrdered_sum d
  simp only [Fin.sum_univ_three] at hs
  have h01 := sharpQutritCentralOrdered_antitone d (show (0 : Fin 3) ≤ 1 by decide)
  have h12 := sharpQutritCentralOrdered_antitone d (show (1 : Fin 3) ≤ 2 by decide)
  constructor <;> linarith

theorem sharpQutritCentralOrdered_dominates_coefficient_sq
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i) (i : Fin 3) :
    d i ^ 2 ≤ sharpQutritCentralOrdered d 0 ^ 2 ∧
      d i ^ 2 ≤ sharpQutritCentralOrdered d 2 ^ 2 := by
  have h := sharpQutritCentralOrdered_dominates_coefficients d i
  have hs := sharpQutritCentralOrdered_extreme_signs d
  constructor
  · exact (sq_le_sq₀ (hd i) hs.1).mpr h.1
  · simpa only [neg_sq] using
      (sq_le_sq₀ (hd i) (neg_nonneg.mpr hs.2)).mpr h.2

/-- Every individual actual signed weight satisfies the two-extreme bound. -/
theorem sharpQutritDiagonalWeight_sq_le
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i) (a : SharpQutritDiagonalIndex) :
    sharpQutritDiagonalWeight d a ^ 2 ≤
      sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 := by
  have hm := sharpQutritCentralOrdered_middle_abs_le d
  have hm0 : sharpQutritCentralOrdered d 1 ^ 2 ≤ sharpQutritCentralOrdered d 0 ^ 2 :=
    sq_le_sq.mpr hm.1
  have h0 := sq_nonneg (sharpQutritCentralOrdered d 0)
  have h2 := sq_nonneg (sharpQutritCentralOrdered d 2)
  rcases a with a | ⟨a, s⟩
  · change sharpQutritCentralOrdered d a ^ 2 ≤ _
    fin_cases a
    · change sharpQutritCentralOrdered d 0 ^ 2 ≤ _
      exact le_add_of_nonneg_right h2
    · change sharpQutritCentralOrdered d 1 ^ 2 ≤ _
      exact hm0.trans (le_add_of_nonneg_right h2)
    · change sharpQutritCentralOrdered d 2 ^ 2 ≤ _
      exact le_add_of_nonneg_left h0
  · change sharpQutritExternalWeight d a s ^ 2 ≤ _
    rw [sharpQutritExternalWeight_sq]
    have h := sharpQutritCentralOrdered_dominates_coefficient_sq d hd a
    linarith

/-- Every distinct pair among all nine actual weights has squared sum at
most the squared sum of the two actual central extremes. -/
theorem sharpQutritDiagonalWeight_pair_le
    (d : Fin 3 → ℝ) (hd : ∀ i, 0 ≤ d i) (a b : SharpQutritDiagonalIndex)
    (hab : a ≠ b) :
    sharpQutritDiagonalWeight d a ^ 2 + sharpQutritDiagonalWeight d b ^ 2 ≤
      sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 := by
  have hm := sharpQutritCentralOrdered_middle_abs_le d
  have hm0 : sharpQutritCentralOrdered d 1 ^ 2 ≤ sharpQutritCentralOrdered d 0 ^ 2 :=
    sq_le_sq.mpr hm.1
  have hm2 : sharpQutritCentralOrdered d 1 ^ 2 ≤ sharpQutritCentralOrdered d 2 ^ 2 :=
    sq_le_sq.mpr hm.2
  rcases a with a | ⟨a, s⟩
  · rcases b with b | ⟨b, t⟩
    · have hne : a ≠ b := fun h => hab (congrArg Sum.inl h)
      change sharpQutritCentralOrdered d a ^ 2 + sharpQutritCentralOrdered d b ^ 2 ≤ _
      fin_cases a <;> fin_cases b
      · exact (hne rfl).elim
      · change sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 1 ^ 2 ≤ _
        exact add_le_add le_rfl hm2
      · change sharpQutritCentralOrdered d 0 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 ≤ _
        exact le_rfl
      · change sharpQutritCentralOrdered d 1 ^ 2 + sharpQutritCentralOrdered d 0 ^ 2 ≤ _
        linarith
      · exact (hne rfl).elim
      · change sharpQutritCentralOrdered d 1 ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 ≤ _
        exact add_le_add hm0 le_rfl
      · change sharpQutritCentralOrdered d 2 ^ 2 + sharpQutritCentralOrdered d 0 ^ 2 ≤ _
        exact (add_comm _ _).le
      · change sharpQutritCentralOrdered d 2 ^ 2 + sharpQutritCentralOrdered d 1 ^ 2 ≤ _
        linarith
      · exact (hne rfl).elim
    · have hb := sharpQutritCentralOrdered_dominates_coefficient_sq d hd b
      change sharpQutritCentralOrdered d a ^ 2 + sharpQutritExternalWeight d b t ^ 2 ≤ _
      rw [sharpQutritExternalWeight_sq]
      fin_cases a
      · change sharpQutritCentralOrdered d 0 ^ 2 + d b ^ 2 ≤ _
        exact add_le_add le_rfl hb.2
      · change sharpQutritCentralOrdered d 1 ^ 2 + d b ^ 2 ≤ _
        exact add_le_add hm0 hb.2
      · change sharpQutritCentralOrdered d 2 ^ 2 + d b ^ 2 ≤ _
        linarith
  · rcases b with b | ⟨b, t⟩
    · have ha := sharpQutritCentralOrdered_dominates_coefficient_sq d hd a
      change sharpQutritExternalWeight d a s ^ 2 + sharpQutritCentralOrdered d b ^ 2 ≤ _
      rw [sharpQutritExternalWeight_sq]
      fin_cases b
      · change d a ^ 2 + sharpQutritCentralOrdered d 0 ^ 2 ≤ _
        linarith
      · change d a ^ 2 + sharpQutritCentralOrdered d 1 ^ 2 ≤ _
        exact add_le_add ha.1 hm2
      · change d a ^ 2 + sharpQutritCentralOrdered d 2 ^ 2 ≤ _
        exact add_le_add ha.1 le_rfl
    · have ha := sharpQutritCentralOrdered_dominates_coefficient_sq d hd a
      have hb := sharpQutritCentralOrdered_dominates_coefficient_sq d hd b
      change sharpQutritExternalWeight d a s ^ 2 + sharpQutritExternalWeight d b t ^ 2 ≤ _
      rw [sharpQutritExternalWeight_sq, sharpQutritExternalWeight_sq]
      linarith

end ThreeCopyQutritWerner
