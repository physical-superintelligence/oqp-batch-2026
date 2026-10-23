module

public import ThreeCopyQutritWerner.TwoCutSingleSourceProjection

@[expose] public section


/-! One constructed projection for an entire fixed-source family of cut zeros. -/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- All members, including zero members, have one actual second-site
projection. The family of first-site input vectors remains unrestricted. -/
theorem cutForm_zero_single_source_family
    {ι a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (F : ι → Matrix (a × d) (a × d) ℂ) (i₀ : ι)
    (hr : ∀ i, (F i).rank ≤ 2) (hq : ∀ i, cutForm (F i) = 0) (hne : F i₀ ≠ 0)
    (hR : ∀ i, LinearMap.range (F i).mulVecLin ≤ LinearMap.range (F i₀).mulVecLin)
    (k : a) (hrow : ∀ l, l ≠ k → ∀ r q, F i₀ (l, r) q = 0) :
    ∃ (P : Matrix d d ℂ) (v : ι → a → ℂ),
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
        ∀ i, F i = ketBra (fun l => if l = k then 1 else 0) (v i) ⊗ₖ P := by
  classical
  obtain ⟨u, P, hu, hP, hPP, hPr, hAP⟩ :=
    cutForm_zero_single_output_coordinate_factor (F i₀) (hr i₀) (hq i₀) hne k hrow
  have heach (i : ι) : ∃ v : a → ℂ,
      F i = ketBra (fun l => if l = k then 1 else 0) v ⊗ₖ P := by
    obtain ⟨Q, u', v, hQ, hQQ, hQr, hu', hAQ, hBQ⟩ :=
      cutForm_zero_single_source_one_projection (F i₀) (F i)
        (hr i₀) (hq i₀) hne (hr i) (hq i) (hR i) k hrow
    have hN : ketBra (fun l : a => if l = k then 1 else 0) u' ≠ 0 := by
      intro he
      apply hne
      rw [hAQ, he]
      ext p q
      simp [Matrix.kroneckerMap_apply]
    have hPQ : P = Q := by
      apply orthogonal_projection_eq_of_kronecker_range_le
        (ketBra (fun l => if l = k then 1 else 0) u)
        (ketBra (fun l => if l = k then 1 else 0) u') P Q hP hQ hPP hQQ
        (by omega) hN
      rw [← hAP, ← hAQ]
    exact ⟨v, by simpa only [← hPQ] using hBQ⟩
  choose v hv using heach
  exact ⟨P, v, hP, hPP, hPr, hv⟩

end ThreeCopyQutritWerner
