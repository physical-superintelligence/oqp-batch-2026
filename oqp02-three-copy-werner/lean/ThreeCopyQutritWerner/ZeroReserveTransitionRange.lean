module

public import ThreeCopyQutritWerner.ZeroReserveExteriorKernel
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section


/-!
# Exact source ranges of saturated reduced transitions

Equal source kernels imply that multiplying by the other factor's adjoint
loses no source range. The positive-entropy exterior equality establishes the
needed kernel equality, so the range and corange of the reduced transition
are exactly the original two cut-flattening ranges.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace ThreeCopyQutritWerner

private theorem zeroReserve_rank_eq_of_kernel_eq
    {m p n : Type*} [Fintype m] [Fintype p] [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (hker : ∀ v : n → ℂ, A *ᵥ v = 0 ↔ B *ᵥ v = 0) : A.rank = B.rank := by
  have hk : LinearMap.ker A.mulVecLin = LinearMap.ker B.mulVecLin := by
    ext v
    exact hker v
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hB := B.mulVecLin.finrank_range_add_finrank_ker
  rw [hk] at hA
  unfold Matrix.rank
  omega

/-- Equal original column kernels imply that the transition retains the entire
first source range, for arbitrary rectangular complex factors. -/
theorem zeroReserve_range_mul_conjTranspose_of_kernel_eq
    {m p n : Type*} [Fintype m] [Fintype p] [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (hker : ∀ v : n → ℂ, A *ᵥ v = 0 ↔ B *ᵥ v = 0) :
    LinearMap.range (A * Bᴴ).mulVecLin = LinearMap.range A.mulVecLin := by
  have hprod : ∀ v : p → ℂ, (A * Bᴴ) *ᵥ v = 0 ↔ (B * Bᴴ) *ᵥ v = 0 := by
    intro v
    simpa only [← Matrix.mulVec_mulVec] using hker (Bᴴ *ᵥ v)
  have hr := zeroReserve_rank_eq_of_kernel_eq (A * Bᴴ) (B * Bᴴ) hprod
  rw [Matrix.rank_self_mul_conjTranspose] at hr
  have hab := zeroReserve_rank_eq_of_kernel_eq A B hker
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro w ⟨v, rfl⟩
    refine ⟨Bᴴ *ᵥ v, ?_⟩
    exact Matrix.mulVec_mulVec v A Bᴴ
  · change (A * Bᴴ).rank = A.rank
    exact hr.trans hab.symm

/-- The same kernel equality recovers the entire second source range from the
ordinary adjoint transition, with the original conjugation convention. -/
theorem zeroReserve_adjoint_range_mul_conjTranspose_of_kernel_eq
    {m p n : Type*} [Fintype m] [Fintype p] [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (hker : ∀ v : n → ℂ, A *ᵥ v = 0 ↔ B *ᵥ v = 0) :
    LinearMap.range ((A * Bᴴ)ᴴ).mulVecLin = LinearMap.range B.mulVecLin := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact zeroReserve_range_mul_conjTranspose_of_kernel_eq B A (fun v => (hker v).symm)

/-- Positive-entropy saturation of the actual exterior transition inequality
identifies both source ranges exactly, without an additional range premise. -/
theorem zeroReserve_transition_equality_ranges {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (A B : Matrix m n ℂ)
    (hA : 0 < frobSq (zeroReserveCompound A))
    (hB : 0 < frobSq (zeroReserveCompound B))
    (heq : nuclearTrace (A * Bᴴ) ^ 2 - frobSq (A * Bᴴ) =
      Real.sqrt ((frobSq A ^ 2 - frobSq (Aᴴ * A)) *
        (frobSq B ^ 2 - frobSq (Bᴴ * B)))) :
    LinearMap.range (A * Bᴴ).mulVecLin = LinearMap.range A.mulVecLin ∧
      LinearMap.range ((A * Bᴴ)ᴴ).mulVecLin = LinearMap.range B.mulVecLin := by
  have hker := zeroReserve_transition_equality_kernel A B hA hB heq
  exact ⟨zeroReserve_range_mul_conjTranspose_of_kernel_eq A B hker,
    zeroReserve_adjoint_range_mul_conjTranspose_of_kernel_eq A B hker⟩

/-- The literal bipartite source-ray form: positive complementary purity
defects and saturated transition bound recover both actual cut-flattening ranges. -/
theorem zeroReserve_cut_transition_equality_ranges
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]
    (u v : L × R → ℂ)
    (hu : 0 < vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)))
    (hv : 0 < vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))
    (heq : nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) =
      Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
        (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v))))) :
    LinearMap.range (ptraceL (ketBra u v)).mulVecLin =
        LinearMap.range (zeroReserveCutFlatten u).mulVecLin ∧
      LinearMap.range ((ptraceL (ketBra u v))ᴴ).mulVecLin =
        LinearMap.range (zeroReserveCutFlatten v).mulVecLin := by
  have hgram (z : L × R → ℂ) :
      frobSq ((zeroReserveCutFlatten z)ᴴ * zeroReserveCutFlatten z) =
        frobSq (ptraceR (ketBra z z)) := by
    rw [zeroReserveCutFlatten_gram]
    simp only [frobSq, Matrix.transpose_apply]
    exact Finset.sum_comm
  have hcu := zeroReserveCompound_frobSq (zeroReserveCutFlatten u)
  have hcv := zeroReserveCompound_frobSq (zeroReserveCutFlatten v)
  rw [zeroReserveCutFlatten_frobSq, hgram] at hcu hcv
  have hcu_pos : 0 < frobSq (zeroReserveCompound (zeroReserveCutFlatten u)) := by
    linarith
  have hcv_pos : 0 < frobSq (zeroReserveCompound (zeroReserveCutFlatten v)) := by
    linarith
  have he : nuclearTrace (zeroReserveCutFlatten u * (zeroReserveCutFlatten v)ᴴ) ^ 2 -
      frobSq (zeroReserveCutFlatten u * (zeroReserveCutFlatten v)ᴴ) =
      Real.sqrt ((frobSq (zeroReserveCutFlatten u) ^ 2 -
        frobSq ((zeroReserveCutFlatten u)ᴴ * zeroReserveCutFlatten u)) *
        (frobSq (zeroReserveCutFlatten v) ^ 2 -
          frobSq ((zeroReserveCutFlatten v)ᴴ * zeroReserveCutFlatten v))) := by
    simpa only [← zeroReserveCutFlatten_transition, zeroReserveCutFlatten_frobSq, hgram] using heq
  simpa only [← zeroReserveCutFlatten_transition] using
    zeroReserve_transition_equality_ranges (zeroReserveCutFlatten u)
      (zeroReserveCutFlatten v) hcu_pos hcv_pos he

end ThreeCopyQutritWerner
