module

public import ThreeCopyQutritWerner.ZeroReserveTransitionRange
public import ThreeCopyQutritWerner.ZeroReserveTransition
public import ThreeCopyQutritWerner.CoherentPencilSupport

@[expose] public section


/-!
# Original traced-site support from the common source kernel

Kernel inclusion bounds rank for maps with the same finite input space.
For the two original cut flattenings, every common input kernel vector also
annihilates the transpose of the actual local flattening of their weighted
two-ray operator. This directly controls the original traced-site support.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace ThreeCopyQutritWerner

/-- Kernel inclusion reverses rank when the input space is unchanged. -/
theorem matrix_rank_le_of_kernel_implication
    {m p n : Type*} [Fintype m] [Fintype p] [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix p n ℂ)
    (h : ∀ v : n → ℂ, A *ᵥ v = 0 → B *ᵥ v = 0) : B.rank ≤ A.rank := by
  have hk : LinearMap.ker A.mulVecLin ≤ LinearMap.ker B.mulVecLin := h
  have hd := Submodule.finrank_mono hk
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hB := B.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

/-- The original local support of a weighted two-ray operator is bounded by
the first source rank whenever its input kernel is shared by the second source. -/
theorem zeroReserve_localRange1_le_source_rank_of_kernel
    {L R S : Type*} [Fintype L] [Fintype R] [Fintype S]
    (u v : L × R × S → ℂ) (z w : ℂ)
    (hk : ∀ x : L → ℂ, zeroReserveCutFlatten u *ᵥ x = 0 →
      zeroReserveCutFlatten v *ᵥ x = 0) :
    localRangeDim₁ (z • ketBra u u + w • ketBra v v) ≤
      (zeroReserveCutFlatten u).rank := by
  rw [localRangeDim₁_eq_coherentFlatten_rank, ← Matrix.rank_transpose]
  apply matrix_rank_le_of_kernel_implication (zeroReserveCutFlatten u)
  intro x hux
  have hvx := hk x hux
  funext p
  have hu : ∑ i, u (i, p.1.1, p.1.2) * x i = 0 := congrFun hux p.1
  have hv : ∑ i, v (i, p.1.1, p.1.2) * x i = 0 := congrFun hvx p.1
  change (∑ i, (z * (u (i, p.1.1, p.1.2) * conj (u p.2)) +
    w * (v (i, p.1.1, p.1.2) * conj (v p.2))) * x i) = 0
  calc
    _ = z * conj (u p.2) * (∑ i, u (i, p.1.1, p.1.2) * x i) +
        w * conj (v p.2) * (∑ i, v (i, p.1.1, p.1.2) * x i) := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ = 0 := by rw [hu, hv]; ring

/-- Positive cut entropy and equality of the original nuclear transition
bound give the exact common kernel of both original source flattenings. -/
theorem zeroReserve_cut_transition_equality_kernels
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]
    (u v : L × R → ℂ)
    (hu : 0 < vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)))
    (hv : 0 < vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))
    (heq : nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) =
      Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
        (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))))
    (x : L → ℂ) :
    zeroReserveCutFlatten u *ᵥ x = 0 ↔ zeroReserveCutFlatten v *ᵥ x = 0 := by
  have hgram (r : L × R → ℂ) :
      frobSq ((zeroReserveCutFlatten r)ᴴ * zeroReserveCutFlatten r) =
        frobSq (ptraceR (ketBra r r)) := by
    rw [zeroReserveCutFlatten_gram]
    simp only [frobSq, Matrix.transpose_apply]
    exact Finset.sum_comm
  have hcu := zeroReserveCompound_frobSq (zeroReserveCutFlatten u)
  have hcv := zeroReserveCompound_frobSq (zeroReserveCutFlatten v)
  rw [zeroReserveCutFlatten_frobSq, hgram] at hcu hcv
  apply zeroReserve_transition_equality_kernel (zeroReserveCutFlatten u)
    (zeroReserveCutFlatten v) (by linarith) (by linarith) ?_ x
  simpa only [← zeroReserveCutFlatten_transition, zeroReserveCutFlatten_frobSq, hgram] using heq

/-- Saturated positive-entropy transitions control the actual local source
rank at the traced site, without a sharp-partial-trace hypothesis. -/
theorem zeroReserve_localRange1_le_transition_rank
    {L R S : Type*} [Fintype L] [Fintype R] [Fintype S]
    [DecidableEq R] [DecidableEq S]
    (u v : L × R × S → ℂ) (z w : ℂ)
    (hu : 0 < vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)))
    (hv : 0 < vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))
    (heq : nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) =
      Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
        (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v))))) :
    localRangeDim₁ (z • ketBra u u + w • ketBra v v) ≤ (ptrace₁ (ketBra u v)).rank := by
  have hk := zeroReserve_cut_transition_equality_kernels u v hu hv heq
  have hr := (zeroReserve_cut_transition_equality_ranges u v hu hv heq).1
  have he : (ptrace₁ (ketBra u v)).rank = (zeroReserveCutFlatten u).rank :=
    congrArg (fun W : Submodule ℂ ((R × S) → ℂ) => Module.finrank ℂ W) hr
  rw [he]
  exact zeroReserve_localRange1_le_source_rank_of_kernel u v z w (fun x => (hk x).mp)

end ThreeCopyQutritWerner
