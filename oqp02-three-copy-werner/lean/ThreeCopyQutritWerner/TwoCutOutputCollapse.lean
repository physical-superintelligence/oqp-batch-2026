module

public import ThreeCopyQutritWerner.TwoCutColumnProjection

@[expose] public section


/-!
# The exact alternative at a missing output coordinate

A nonzero off-plane input column contains a rank-two projection block and
therefore spans the entire original range. Its common projection factor then
forces one first-site output direction for the full original matrix. Thus a
missing output coordinate is either also missing on input, or the original
first-site output is one-dimensional.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ThreeCopyQutritWerner

variable {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]

/-- A rank-two original block makes its input column span the entire rank-two range. -/
theorem firstSiteColumn_range_eq_of_rank_two_block
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2) (i k : a)
    (hr : (firstSiteBlock C i k).rank = 2) :
    LinearMap.range (firstSiteColumn C k).mulVecLin = LinearMap.range C.mulVecLin := by
  have hblock := firstSiteBlock_rank_le_column C i k
  have hcolumn := firstSiteColumn_rank_le C k
  have hsame : (firstSiteColumn C k).rank = C.rank := by omega
  rw [firstSiteColumn_eq_mul] at hsame ⊢
  exact matrix_range_mul_eq_of_rank_eq C _ hsame

/-- A nonzero off-plane input column forces a literal single first-site
output factor for the whole original matrix. The selected factor entry is one. -/
theorem cutForm_zero_offplane_column_single_output_factor
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2) (hz : cutForm C = 0)
    (k i₀ : a) (hrow : ∀ r q, C (k, r) q = 0)
    (hne : firstSiteBlock C i₀ k ≠ 0) :
    ∃ x : a → ℂ, x i₀ = 1 ∧
      ∀ i r q, C (i, r) q = x i * C (i₀, r) q := by
  let z : a → ℂ := fun i => (firstSiteBlock C i k).trace / 2
  let P := traceNormalizedProjection (firstSiteBlock C i₀ k)
  have ht := firstSiteBlock_trace_saturated_of_cutForm_zero C hC hz k hrow i₀
  obtain ⟨e₀, e₁, h₀, h₁, h01, htrace, hfactor⟩ :=
    eq_trace_smul_proj_of_trace_bound_saturated (firstSiteBlock C i₀ k)
      ((firstSiteBlock_rank_le C i₀ k).trans hC) hne ht
  have hz₀ : z i₀ ≠ 0 := div_ne_zero htrace (by norm_num)
  have hr := rank_two_of_trace_bound_saturated (firstSiteBlock C i₀ k)
    ((firstSiteBlock_rank_le C i₀ k).trans hC) hne ht
  have hrange := firstSiteColumn_range_eq_of_rank_two_block C hC i₀ k hr
  have hall := firstSiteColumn_one_projection_of_cutForm_zero C hC hz k i₀ hrow hne
  have hentry (i : a) (r s : d) : firstSiteColumn C k (i, r) s = z i * P r s := by
    exact congrFun (congrFun (hall i) r) s
  refine ⟨fun i => z i / z i₀, div_self hz₀, ?_⟩
  intro i r q
  have hq : Cᵀ q ∈ LinearMap.range C.mulVecLin := by
    refine ⟨Pi.single q 1, ?_⟩
    ext p
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hrange] at hq
  obtain ⟨v, hv⟩ := hq
  have he (j : a) : C (j, r) q = z j * ∑ s, P r s * v s := by
    calc
      C (j, r) q = ∑ s, firstSiteColumn C k (j, r) s * v s :=
        (congrFun hv (j, r)).symm
      _ = ∑ s, (z j * P r s) * v s := by simp only [hentry]
      _ = z j * ∑ s, P r s * v s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
  rw [he i, he i₀]
  field_simp [hz₀] <;> ring

/-- Every missing first output coordinate either also vanishes on input or
the entire original matrix has one nonzero first-site output factor. -/
theorem cutForm_zero_missing_row_alignment_or_single_output
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2) (hz : cutForm C = 0)
    (k : a) (hrow : ∀ r q, C (k, r) q = 0) :
    (∀ p r, C p (k, r) = 0) ∨
      ∃ (i₀ : a) (x : a → ℂ), x i₀ = 1 ∧
        ∀ i r q, C (i, r) q = x i * C (i₀, r) q := by
  classical
  by_cases hcol : ∀ i, firstSiteBlock C i k = 0
  · left
    rintro ⟨i, s⟩ r
    exact congrFun (congrFun (hcol i) s) r
  · right
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hcol
    obtain ⟨x, hx, he⟩ :=
      cutForm_zero_offplane_column_single_output_factor C hC hz k i₀ hrow hi₀
    exact ⟨i₀, x, hx, he⟩

end ThreeCopyQutritWerner
