module

public import ThreeCopyQutritWerner.SingularUnitaryCompletion

@[expose] public section


/-!
# Constructing a common unitary annihilator of two qutrit vectors

An actual full singular-value decomposition supplies a missing row for any
rank-at-most-two qutrit matrix. Applied to the original columns a,b,0 this
constructs a unitary annihilator for both vectors, including zero and
dependent vectors without a supplied normalized orthogonal complement.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

/-- Any actual qutrit matrix of rank at most two has a constructed missing
row in actual unitary coordinates. -/
theorem sharpQutrit_rank_le_two_exists_unitary_zero_row
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.rank ≤ 2) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ ∀ j, (U * A) a j = 0 := by
  obtain ⟨L, R, d, hL, hR, hd, he⟩ := singularFamily_exists_unitary_diagonalization A
  have hD : (Matrix.diagonal (fun i => (d i : ℂ))).rank ≤ 2 := by
    rw [← he]
    exact ((Matrix.rank_mul_le_left (Lᴴ * A) R).trans
      (Matrix.rank_mul_le_right Lᴴ A)).trans hA
  have hz : ∃ a, d a = 0 := by
    by_contra! hn
    have hc (a : Fin 3) : (d a : ℂ) ≠ 0 := by exact_mod_cast hn a
    have hr : (Matrix.diagonal (fun i => (d i : ℂ))).rank = 3 := by
      rw [Matrix.rank_diagonal]
      simp [Fintype.card_subtype, Fin.sum_univ_three, hc]
    rw [hr] at hD
    omega
  obtain ⟨a, ha⟩ := hz
  have hLL : L * Lᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hL
  have hRR : R * Rᴴ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hR
  have hleft : Lᴴ * A = Matrix.diagonal (fun i => (d i : ℂ)) * Rᴴ := by
    rw [← he, Matrix.mul_assoc (Lᴴ * A), hRR, Matrix.mul_one]
  refine ⟨Lᴴ, a, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using hLL
  · intro j
    rw [hleft, Matrix.diagonal_mul, ha, Complex.ofReal_zero, zero_mul]

/-- Two arbitrary original qutrit vectors have a common constructed unitary
row annihilator, with no nonzero or linear independence premise. -/
theorem sharpFixedPair_exists_unitary_annihilator (a b : Fin 3 → ℂ) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℂ, ∃ i : Fin 3, Uᴴ * U = 1 ∧
      (∑ r, U i r * a r) = 0 ∧ (∑ r, U i r * b r) = 0 := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun r c => ![a r, b r, 0] c
  have hA : A.rank ≤ 2 := by
    apply (rank_le_iff_exists_mul A 2).mpr
    refine ⟨(fun r c => ![a r, b r] c), !![1, 0, 0; 0, 1, 0], ?_⟩
    ext r c
    change A r c = ∑ j : Fin 2, (![a r, b r] j) * (!![1, 0, 0; 0, 1, 0] j c)
    fin_cases c <;> simp [A, Fin.sum_univ_two]
  obtain ⟨U, i, hU, hz⟩ := sharpQutrit_rank_le_two_exists_unitary_zero_row A hA
  refine ⟨U, i, hU, ?_, ?_⟩
  · have h0 := hz 0
    rw [Matrix.mul_apply] at h0
    change (∑ r, U i r * a r) = 0 at h0
    exact h0
  · have h1 := hz 1
    rw [Matrix.mul_apply] at h1
    change (∑ r, U i r * b r) = 0 at h1
    exact h1

end ThreeCopyQutritWerner
