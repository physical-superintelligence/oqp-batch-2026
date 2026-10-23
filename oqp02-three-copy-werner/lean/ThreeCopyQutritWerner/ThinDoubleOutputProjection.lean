module

public import ThreeCopyQutritWerner.TwoCutSingleSourceFamily
public import ThreeCopyQutritWerner.ThinSingleOutputRange

@[expose] public section


/-!
# Actual projection factor with two fixed local output coordinates

The original endpoint-zero and rank hypotheses supply all cut-zero blocks
and their common source. A single second-site output coordinate on this
source then constructs one third-site projection for the entire matrix.
-/

noncomputable section

open scoped Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Two original local output rays force an actual common projection on
the remaining site; all original input columns and phases are retained. -/
theorem endpoint_zero_two_output_coordinates_projection
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) (hC : C.rank ≤ 2)
    (hz : endpointEnergy C = 0) (hne : C ≠ 0) (k : a) (l : b)
    (hrow₁ : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0)
    (hrow₂ : ∀ j, j ≠ l → ∀ i r q, C (i, j, r) q = 0) :
    ∃ (P : Matrix c c ℂ) (v : a → b → ℂ),
      P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧
        ∀ p q, C p q = (if p.1 = k then 1 else 0) *
          (if p.2.1 = l then 1 else 0) * star (v q.1 q.2.1) * P p.2.2 q.2.2 := by
  classical
  let F : a → Matrix (b × c) (b × c) ℂ := fun j => firstSiteBlock C k j
  have hFq : ∀ j, cutForm (F j) = 0 :=
    firstSiteBlock_cutForm_zero_of_single_output_endpoint_zero C hC hz k hrow₁
  have hFr (j : a) : (F j).rank ≤ 2 := (firstSiteBlock_rank_le C k j).trans hC
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, F j₀ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext ⟨i, r⟩ ⟨j, s⟩
    by_cases hi : i = k
    · subst i
      exact congrFun (congrFun (h j) r) s
    · exact hrow₁ i hi r (j, s)
  have hFR (j : a) : LinearMap.range (F j).mulVecLin ≤
      LinearMap.range (F j₀).mulVecLin := by
    by_cases hj : F j = 0
    · simp [hj]
    · exact (single_output_nonzero_blocks_same_range C hC hz k hrow₁ j j₀ hj hj₀).2.2.le
  obtain ⟨P, v, hP, hPP, hPr, hF⟩ := cutForm_zero_single_source_family F j₀
    hFr hFq hj₀ hFR l (fun j hj r q => hrow₂ j hj k r (j₀, q))
  refine ⟨P, v, hP, hPP, hPr, ?_⟩
  rintro ⟨i, j, r⟩ ⟨s, t, u⟩
  by_cases hi : i = k
  · subst i
    simpa only [F, firstSiteBlock, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, ketBra, if_true, one_mul, mul_assoc, starRingEnd_apply]
      using congrFun (congrFun (hF s) (j, r)) (t, u)
  · simp [hi, hrow₁ i hi]

end ThreeCopyQutritWerner
