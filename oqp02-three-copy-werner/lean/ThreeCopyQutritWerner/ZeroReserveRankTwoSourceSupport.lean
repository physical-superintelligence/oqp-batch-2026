module

public import ThreeCopyQutritWerner.SharpRankTwoRangeSupport
public import ThreeCopyQutritWerner.ZeroReserveTransitionRange
public import ThreeCopyQutritWerner.ZeroReserveTransition

@[expose] public section


/-!
# Original source support from a saturated rank-two cut transition

Positive-entropy saturation identifies the transition ranges with the two
original cut-source ranges. Sharp saturation at rank two then supplies the
same local missing coordinates for all columns of both original sources.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker

namespace ThreeCopyQutritWerner

/-- Equality of actual ranges transports every transformed row annihilator. -/
theorem matrix_zero_row_of_range_eq
    {m n p k : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix m p ℂ) (W : Matrix k m ℂ)
    (hR : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin)
    (i : k) (hA : ∀ j, (W * A) i j = 0) (j : p) : (W * B) i j = 0 := by
  have hb : (fun r => B r j) ∈ LinearMap.range B.mulVecLin := by
    refine ⟨Pi.single j 1, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    rfl
  rw [← hR] at hb
  obtain ⟨v, hv⟩ := hb
  have he : (W * A) *ᵥ v = W *ᵥ (fun r => B r j) := by
    rw [← Matrix.mulVec_mulVec]
    change W *ᵥ (A.mulVecLin v) = _
    rw [hv]
  have hi := congrFun he i
  have hz : ((W * A) *ᵥ v) i = 0 := by simp [Matrix.mulVec, dotProduct, hA]
  rw [hz] at hi
  exact hi.symm

/-- A saturated cut transition of actual rank two forces a common two-by-two
support of both original source flattenings. All range premises are derived. -/
theorem zeroReserve_rank_two_cut_exists_source_support
    {L : Type*} [Fintype L] [DecidableEq L]
    (u v : L × (Fin 3 × Fin 3) → ℂ)
    (hu : 0 < vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u)))
    (hv : 0 < vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))
    (heq : nuclearTrace (ptraceL (ketBra u v)) ^ 2 - frobSq (ptraceL (ketBra u v)) =
      Real.sqrt ((vecNormSq u ^ 2 - frobSq (ptraceR (ketBra u u))) *
        (vecNormSq v ^ 2 - frobSq (ptraceR (ketBra v v)))))
    (hr : (ptraceL (ketBra u v)).rank = 2)
    (hsat : frobSq (ptraceL (ptraceL (ketBra u v))) +
        frobSq (ptraceR (ptraceL (ketBra u v))) =
      nuclearTrace (ptraceL (ketBra u v)) ^ 2 +
        Complex.normSq (ptraceL (ketBra u v)).trace) :
    ∃ U V : Matrix (Fin 3) (Fin 3) ℂ, ∃ a : Fin 3,
      Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ (i j : Fin 3) (p : L), i = a ∨ j = a →
        ((U ⊗ₖ V) * zeroReserveCutFlatten u) (i, j) p = 0 ∧
        ((U ⊗ₖ V) * zeroReserveCutFlatten v) (i, j) p = 0 := by
  obtain ⟨hRu, hRv⟩ := zeroReserve_cut_transition_equality_ranges u v hu hv heq
  obtain ⟨U, V, a, hU, hV, ha⟩ :=
    sharpPartialTrace_rank_two_exists_range_support (ptraceL (ketBra u v)) hr hsat
  refine ⟨U, V, a, hU, hV, ?_⟩
  intro i j p hij
  exact ⟨matrix_zero_row_of_range_eq _ _ _ hRu (i, j) (fun q => (ha i j q hij).1) p,
    matrix_zero_row_of_range_eq _ _ _ hRv (i, j) (fun q => (ha i j q hij).2) p⟩

end ThreeCopyQutritWerner
