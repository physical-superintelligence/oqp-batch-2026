module

public import ThreeCopyQutritWerner.TwoCutTensorProjectionSource

@[expose] public section


/-!
# One projection for all cut zeros on a single local output source

One original anchor with a single first output coordinate constructs a
rank-two orthogonal projection. Every cut zero with range in that anchor
uses the same projection. The second matrix may be zero, and its input
vector is arbitrary; no input-plane alignment is imposed.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- The exceptional fixed-source branch has one actual shared projection,
including zero members and independently varying complex input vectors. -/
theorem cutForm_zero_single_source_one_projection
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (A B : Matrix (a × d) (a × d) ℂ)
    (hA : A.rank ≤ 2) (hqA : cutForm A = 0) (hne : A ≠ 0)
    (hB : B.rank ≤ 2) (hqB : cutForm B = 0)
    (hR : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin)
    (k : a) (hrow : ∀ i, i ≠ k → ∀ r q, A (i, r) q = 0) :
    ∃ (P : Matrix d d ℂ) (u v : a → ℂ),
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧ u ≠ 0 ∧
        A = ketBra (fun i => if i = k then 1 else 0) u ⊗ₖ P ∧
        B = ketBra (fun i => if i = k then 1 else 0) v ⊗ₖ P := by
  classical
  obtain ⟨u, P, hu, hP, hPP, hPr, hAP⟩ :=
    cutForm_zero_single_output_coordinate_factor A hA hqA hne k hrow
  by_cases hzero : B = 0
  · refine ⟨P, u, 0, hP, hPP, hPr, hu, hAP, ?_⟩
    ext p q
    simp [hzero, ketBra, Matrix.kroneckerMap_apply]
  obtain ⟨R, hBR⟩ := matrix_exists_right_factor_of_range_le B A hR
  have hBrow (i : a) (hi : i ≠ k) (r : d) (q : a × d) : B (i, r) q = 0 := by
    rw [hBR, Matrix.mul_apply]
    simp only [hrow i hi r, zero_mul, Finset.sum_const_zero]
  obtain ⟨v, Q, hv, hQ, hQQ, hQr, hBQ⟩ :=
    cutForm_zero_single_output_coordinate_factor B hB hqB hzero k hBrow
  have hN : ketBra (fun i : a => if i = k then 1 else 0) v ≠ 0 := by
    intro he
    apply hzero
    rw [hBQ, he]
    ext p q
    simp [Matrix.kroneckerMap_apply]
  have hPQ : P = Q := by
    apply orthogonal_projection_eq_of_kronecker_range_le
      (ketBra (fun i => if i = k then 1 else 0) u)
      (ketBra (fun i => if i = k then 1 else 0) v) P Q hP hQ hPP hQQ
      (by omega) hN
    simpa only [← hAP, ← hBQ] using hR
  exact ⟨P, u, v, hP, hPP, hPr, hu, hAP, by simpa only [← hPQ] using hBQ⟩

end ThreeCopyQutritWerner
