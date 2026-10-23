module

public import ThreeCopyQutritWerner.TwoCutSingleOutput

@[expose] public section


/-!
# Exact tensor factor of a single-output-coordinate cut zero

Applying the common-column argument to the original adjoint aligns all
input blocks. The original matrix is literally one ket-bra tensored with
one Hermitian rank-two projection, including its full complex scale.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

namespace ThreeCopyQutritWerner

/-- Every nonzero cut zero supported on one first-site output coordinate has
an actual projection tensor factor. All phases remain in the ket-bra vector. -/
theorem cutForm_zero_single_output_coordinate_factor
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2)
    (hz : cutForm C = 0) (hne : C ≠ 0) (k : a)
    (hrow : ∀ i, i ≠ k → ∀ r q, C (i, r) q = 0) :
    ∃ (b : a → ℂ) (P : Matrix d d ℂ), b ≠ 0 ∧ P.IsHermitian ∧
      P * P = P ∧ P.rank = 2 ∧
      C = ketBra (fun i => if i = k then 1 else 0) b ⊗ₖ P := by
  have hT := firstSiteBlock_trace_saturated_of_single_output C hC hz k hrow
  obtain ⟨j₀, hj₀⟩ : ∃ j, firstSiteBlock C k j ≠ 0 := by
    by_contra! hall
    apply hne
    ext ⟨i, r⟩ ⟨j, s⟩
    by_cases hi : i = k
    · subst i
      exact congrFun (congrFun (hall j) r) s
    · exact hrow i hi r (j, s)
  have hCH : Cᴴ.rank ≤ 2 := by simpa only [Matrix.rank_conjTranspose] using hC
  have hTH (j : a) : Complex.normSq (firstSiteBlock Cᴴ j k).trace =
      2 * frobSq (firstSiteBlock Cᴴ j k) := by
    simpa only [firstSiteBlock_conjTranspose, Matrix.trace_conjTranspose,
      Complex.star_def, Complex.normSq_conj, rankTwo_frobSq_conjTranspose] using hT j
  have hjH : firstSiteBlock Cᴴ j₀ k ≠ 0 := by
    rw [firstSiteBlock_conjTranspose]
    intro he
    apply hj₀
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero]
      using congrArg Matrix.conjTranspose he
  let P := traceNormalizedProjection (firstSiteBlock Cᴴ j₀ k)
  have hP := traceNormalizedProjection_properties (firstSiteBlock Cᴴ j₀ k)
    ((firstSiteBlock_rank_le Cᴴ j₀ k).trans hCH) hjH (hTH j₀)
  have hPH : Pᴴ = P := hP.1
  have hall := firstSiteColumn_saturated_blocks_one_projection Cᴴ hCH k j₀ hTH hjH
  have hblock (j : a) : firstSiteBlock C k j =
      ((firstSiteBlock C k j).trace / 2) • P := by
    have he := congrArg Matrix.conjTranspose (hall j)
    change (firstSiteBlock Cᴴ j k)ᴴ =
      (((firstSiteBlock Cᴴ j k).trace / 2) • P)ᴴ at he
    simp only [Matrix.conjTranspose_smul, hPH, firstSiteBlock_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_conjTranspose,
      Complex.star_def, map_div₀, map_ofNat, starRingEnd_self_apply] at he
    exact he
  let b : a → ℂ := fun j => conj ((firstSiteBlock C k j).trace / 2)
  have hfactor : C = ketBra (fun i => if i = k then 1 else 0) b ⊗ₖ P := by
    ext ⟨i, r⟩ ⟨j, s⟩
    by_cases hi : i = k
    · subst i
      simpa only [firstSiteBlock, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.kroneckerMap_apply, ketBra, if_true, one_mul, b, Complex.conj_conj]
        using congrFun (congrFun (hblock j) r) s
    · simp [Matrix.kroneckerMap_apply, ketBra, hi, hrow i hi]
  refine ⟨b, P, ?_, hP.1, hP.2.1, hP.2.2.1, hfactor⟩
  intro hb
  apply hne
  rw [hfactor]
  ext p q
  simp [Matrix.kroneckerMap_apply, ketBra, hb]

end ThreeCopyQutritWerner
