module

public import ThreeCopyQutritWerner.TwoCutBlockEmbedding
public import ThreeCopyQutritWerner.TraceProjection

@[expose] public section


/-!
# A nonzero off-plane input column has one actual projection

Each nonzero block saturates the rank-two trace inequality. The full column
has rank at most two, so every such block determines its entire adjoint range.
Uniqueness of Hermitian idempotents makes all normalized block projections
equal, retaining each block's original complex trace coefficient.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

/-- A saturated original block and its adjoint determine the same normalized
projection range, even when its nonzero scalar has arbitrary complex phase. -/
theorem traceNormalizedProjection_range_eq_adjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix n n ℂ) (hB : B.rank ≤ 2) (hne : B ≠ 0)
    (hT : Complex.normSq B.trace = 2 * frobSq B) :
    LinearMap.range (traceNormalizedProjection B).mulVecLin =
      LinearMap.range (Bᴴ).mulVecLin := by
  obtain ⟨e₀, e₁, h₀, h₁, h01, ht, he⟩ :=
    eq_trace_smul_proj_of_trace_bound_saturated B hB hne hT
  have hp := (traceNormalizedProjection_properties B hB hne hT).1
  have hb := congrArg Matrix.conjTranspose (traceNormalizedProjection_reconstruct B ht)
  rw [Matrix.conjTranspose_smul, hp.eq] at hb
  rw [hb]
  exact (matrix_range_smul_eq _ _ (star_ne_zero.mpr
    (div_ne_zero ht (by norm_num)))).symm

/-- One nonzero original block fixes the projection of all blocks in the
same rank-at-most-two input column. Zero blocks are included. -/
theorem firstSiteColumn_saturated_blocks_one_projection
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2) (k i₀ : a)
    (hT : ∀ i, Complex.normSq (firstSiteBlock C i k).trace =
      2 * frobSq (firstSiteBlock C i k))
    (hne : firstSiteBlock C i₀ k ≠ 0) :
    ∀ i, firstSiteBlock C i k = ((firstSiteBlock C i k).trace / 2) •
      traceNormalizedProjection (firstSiteBlock C i₀ k) := by
  have hr₀ := rank_two_of_trace_bound_saturated (firstSiteBlock C i₀ k)
    ((firstSiteBlock_rank_le C i₀ k).trans hC) hne (hT i₀)
  have hcol : (firstSiteColumn C k).rank = 2 := by
    have hlo := firstSiteBlock_rank_le_column C i₀ k
    have hhi := (firstSiteColumn_rank_le C k).trans hC
    omega
  have hp₀ := traceNormalizedProjection_properties (firstSiteBlock C i₀ k)
    ((firstSiteBlock_rank_le C i₀ k).trans hC) hne (hT i₀)
  have hrange₀ := traceNormalizedProjection_range_eq_adjoint (firstSiteBlock C i₀ k)
    ((firstSiteBlock_rank_le C i₀ k).trans hC) hne (hT i₀)
  intro i
  by_cases hi : firstSiteBlock C i k = 0
  · simp [hi]
  have hri := rank_two_of_trace_bound_saturated (firstSiteBlock C i k)
    ((firstSiteBlock_rank_le C i k).trans hC) hi (hT i)
  have hpi := traceNormalizedProjection_properties (firstSiteBlock C i k)
    ((firstSiteBlock_rank_le C i k).trans hC) hi (hT i)
  have hriP := traceNormalizedProjection_range_eq_adjoint (firstSiteBlock C i k)
    ((firstSiteBlock_rank_le C i k).trans hC) hi (hT i)
  have heq : traceNormalizedProjection (firstSiteBlock C i k) =
      traceNormalizedProjection (firstSiteBlock C i₀ k) := by
    apply matrix_hermitian_idempotent_eq_of_range_eq _ _ hpi.1 hp₀.1 hpi.2.1 hp₀.2.1
    rw [hriP, hrange₀,
      firstSiteBlock_adjoint_range_eq_column C i k (hri.trans hcol.symm),
      firstSiteBlock_adjoint_range_eq_column C i₀ k (hr₀.trans hcol.symm)]
  obtain ⟨e₀, e₁, h₀, h₁, h01, ht, hfactor⟩ :=
    eq_trace_smul_proj_of_trace_bound_saturated (firstSiteBlock C i k)
      ((firstSiteBlock_rank_le C i k).trans hC) hi (hT i)
  exact (traceNormalizedProjection_reconstruct _ ht).trans (congrArg
    (fun P => ((firstSiteBlock C i k).trace / 2) • P) heq)

/-- At an original cut zero with a missing output coordinate, every block in
the opposite input column has this one actual scalar-projection form. -/
theorem firstSiteColumn_one_projection_of_cutForm_zero
    {a d : Type*} [Fintype a] [Fintype d] [DecidableEq a] [DecidableEq d]
    (C : Matrix (a × d) (a × d) ℂ) (hC : C.rank ≤ 2) (hz : cutForm C = 0)
    (k i₀ : a) (hrow : ∀ r q, C (k, r) q = 0)
    (hne : firstSiteBlock C i₀ k ≠ 0) :
    ∀ i, firstSiteBlock C i k = ((firstSiteBlock C i k).trace / 2) •
      traceNormalizedProjection (firstSiteBlock C i₀ k) :=
  firstSiteColumn_saturated_blocks_one_projection C hC k i₀
    (firstSiteBlock_trace_saturated_of_cutForm_zero C hC hz k hrow) hne

end ThreeCopyQutritWerner
