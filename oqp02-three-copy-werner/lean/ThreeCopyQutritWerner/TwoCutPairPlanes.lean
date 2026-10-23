module

public import ThreeCopyQutritWerner.TwoCutRankTwoAnchor
public import ThreeCopyQutritWerner.SharpFixedPairAnnihilator
public import ThreeCopyQutritWerner.SharpRankOneFamily

@[expose] public section


/-!
# Common local planes for an actual polarized-null pair

Two rank-at-most-one reshapes already fit common local planes. If either
reshape has rank two, it anchors its polarized-null partner. A nonzero
partner excludes rank three by the existing exact cofactor identity.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

private theorem twoCut_product_coordinate_change
    (U V A : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ)
    (hA : ∀ i j, A i j = x i * y j) (i j : Fin 3) :
    (U * A * Vᵀ) i j = (∑ r, U i r * x r) * (∑ s, V j s * y s) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hA, Finset.sum_mul,
    Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Any two qutrit rank-at-most-one matrices fit simultaneous local planes,
including the zero and dependent cases without a polarization premise. -/
theorem twoCut_rank_one_pair_exists_planes
    (A B : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.rank ≤ 1) (hB : B.rank ≤ 1) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a b : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ i, (U * A * Vᵀ) a i = 0 ∧ (U * A * Vᵀ) i b = 0 ∧
        (U * B * Vᵀ) a i = 0 ∧ (U * B * Vᵀ) i b = 0 := by
  obtain ⟨x, y, hxy⟩ := sharpReshape_rank_le_one_exists_product
    (fun p => A p.1 p.2) hA
  obtain ⟨z, w, hzw⟩ := sharpReshape_rank_le_one_exists_product
    (fun p => B p.1 p.2) hB
  obtain ⟨U, a, hU, hx, hz⟩ := sharpFixedPair_exists_unitary_annihilator x z
  obtain ⟨V, b, hV, hy, hw⟩ := sharpFixedPair_exists_unitary_annihilator y w
  refine ⟨U, V, a, b, hU, hV, ?_⟩
  intro i
  simp only [twoCut_product_coordinate_change U V A x y hxy,
    twoCut_product_coordinate_change U V B z w hzw, hx, hz, hy, hw,
    zero_mul, mul_zero, and_self]

private theorem twoCut_transpose_isometry (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) : (Vᵀ)ᴴ * Vᵀ = 1 := by
  simpa only [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.transpose_mul, Matrix.transpose_one]
    using congrArg Matrix.transpose ((Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 3))).mp hV)

/-- Two nonzero polarized-null qutrit matrices have common local row and
column planes in actual unitary coordinates. The two local indices may differ. -/
theorem sharpPolarizedMinor_nonzero_pair_exists_planes
    (A B : Matrix (Fin 3) (Fin 3) ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ i j k l, sharpPolarizedMinor A B i j k l = 0) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a b : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ i, (U * A * Vᵀ) a i = 0 ∧ (U * A * Vᵀ) i b = 0 ∧
        (U * B * Vᵀ) a i = 0 ∧ (U * B * Vᵀ) i b = 0 := by
  have hs : ∀ i j k l, sharpPolarizedMinor B A i j k l = 0 := by
    intro i j k l
    have he := h i j k l
    unfold sharpPolarizedMinor at he ⊢
    linear_combination he
  have hAr : A.rank ≤ 2 :=
    sharp_rank_le_two_of_det_eq_zero A (sharpPolarizedMinor_det_eq_zero A B hB h)
  have hBr : B.rank ≤ 2 :=
    sharp_rank_le_two_of_det_eq_zero B (sharpPolarizedMinor_det_eq_zero B A hA hs)
  by_cases hA2 : A.rank = 2
  · obtain ⟨U, V, a, hU, hV, hp⟩ :=
      sharpPolarizedMinor_rank_two_exists_missing_coordinates A B hA2 h
    refine ⟨U, Vᵀ, a, a, hU, twoCut_transpose_isometry V hV, ?_⟩
    simpa only [Matrix.transpose_transpose] using hp
  · by_cases hB2 : B.rank = 2
    · obtain ⟨U, V, a, hU, hV, hp⟩ :=
        sharpPolarizedMinor_rank_two_exists_missing_coordinates B A hB2 hs
      refine ⟨U, Vᵀ, a, a, hU, twoCut_transpose_isometry V hV, ?_⟩
      intro i
      simp only [Matrix.transpose_transpose]
      exact ⟨(hp i).2.2.1, (hp i).2.2.2, (hp i).1, (hp i).2.1⟩
    · exact twoCut_rank_one_pair_exists_planes A B (by omega) (by omega)

end ThreeCopyQutritWerner
